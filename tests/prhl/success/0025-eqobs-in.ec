module type Orcl = {
  fun f (x:int) : int 
}.

module F = { 
  var view : int
  fun f () : unit = {
    view = 1;
  } 
}.

lemma toto : forall (Or<:Orcl {F}),
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
intros Or.
fun.
 eqobs_in (={glob Or}) true : (={F.view, glob Or}).
save.

lemma toto1 : forall (Or<:Orcl),
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
intros Or.
fun.
 eqobs_in (={glob Or}) true : (={F.view, glob Or}).
save.

module Or = { 
  var x : int
}.

lemma toto2 : 
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
fun.
 eqobs_in (={glob Or}) true : (={F.view, glob Or}).
save.