# --------------------------------------------------------------------l
import sys, gevent.monkey

if 'threading' in sys.modules:
    # That's a bit brutal
    del sys.modules['threading']
gevent.monkey.patch_all()

import os, re, json, logging, cStringIO as sio, socket

import gevent, gevent.subprocess as sp, gevent.pywsgi as gwsgi

from geventwebsocket.handler    import WebSocketHandler
from geventwebsocket.exceptions import WebSocketError

# --------------------------------------------------------------------
logging.basicConfig()
logger = logging.getLogger(__file__)

# --------------------------------------------------------------------
from pyramid.view import view_config

# --------------------------------------------------------------------
class EasyCryptClient(object):
    def __init__(self, websocket):
        self.websocket = websocket
        self.easycrypt = None
        self.prompt    = None

    def __read_prompt(self):
        prompt = sio.StringIO()

        while True:
            content = self.easycrypt.stdout.readline().rstrip('\r\n')
            match   = re.search(r'^\[(\d+)|.*?\]>$', content)

            if match is None:
                prompt.write('%s\r\n' % (content,))
            else:
                self.prompt = int(match.group(1))
                return prompt.getvalue()

    def __undo(self, id):
        self.easycrypt.stdin.write('undo %d.\r\n' % (id,))
        self.easycrypt.stdin.flush()

        prompt  = self.__read_prompt()
        message = dict(
            status  = 'undo'     ,
            pundo   = self.prompt,
            message = prompt     ,
        )

        self.websocket.send(json.dumps(message))

    def __send(self, statement):
        self.easycrypt.stdin.write(re.sub(r'\r?\n', ' ', statement) + '\r\n')
        self.easycrypt.stdin.flush()

    def __forward(self, contents):
        self.__send(contents)

        pundo  = self.prompt
        prompt = self.__read_prompt()
        match  = re.search('^\[error-\d+-\d+\](.*)', prompt, re.M | re.S)

        if match is None:
            message = dict(
                status  = 'ok'  ,
                message = prompt,
                pundo   = pundo ,
            )
        else:
            assert (pundo == self.prompt)
            message = dict(
                status    = 'error',
                message   = match.group(1),
                start_err = -1,
                end_err   = -1,
            )

        self.websocket.send(json.dumps(message))

    def __run(self):
        while True:
            try:
                message = self.websocket.receive()
            except WebSocketError:
                return
            if message is None:
                return
            message = json.loads(message)

            if  message['mode'] == 'undo':
                self.__undo(int(message['data']))
            elif message['mode'] == 'forward':
                self.__forward(message['contents'])

    def run(self):
        assert (self.easycrypt == None)

        self.easycrypt = \
            sp.Popen(['ec.native', '-emacs'],
                     stdin  = sp.PIPE,
                     stdout = sp.PIPE,
                     stderr = sp.STDOUT)

        try:
            self.__read_prompt()
            self.__run()
        finally:
            try:
                self.easycrypt.kill()
                self.easycrypt.wait()
            except OSError:
                pass
            self.easycrypt = None
            self.prompt    = None

# --------------------------------------------------------------------
@view_config(route_name = 'root', renderer = 'json')
def root(request):
    return {}

# --------------------------------------------------------------------
@view_config(route_name = 'easycrypt', renderer = 'string')
def easycrypt(request):
    websocket = request.environ['wsgi.websocket']
    EasyCryptClient(websocket).run()
    return 'OK'

# --------------------------------------------------------------------
def _routing(config):
    config.add_route('root', '/')
    config.add_route('easycrypt', '/engine')

# --------------------------------------------------------------------
def main(global_config, **settings):
    from pyramid.config import Configurator

    config = Configurator(settings=settings)
    config.include(_routing); config.scan()

    application = config.make_wsgi_app()
    application.app_protocol = lambda _ : 'easycrypt'

    return application

# --------------------------------------------------------------------
def wsserver(global_conf, **kw):
    bind = socket.getaddrinfo(kw.pop('host', 'localhost'),
                              kw.pop('port', '8090'),
                              socket.AF_INET, socket.SOCK_STREAM)[0][4]
    def serve(app):
        server = gwsgi.WSGIServer(bind, app, handler_class=WebSocketHandler)
        server.serve_forever()
    return serve