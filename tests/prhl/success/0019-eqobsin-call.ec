require import Int.
module M = { 
  var m : int
  fun f (x:int) : int = { 
    m = m + x;
    return m;
  }

  fun g (x:int) : int = { return m + x; }

  fun main (w:int) : int = {
    m = 0;
    w = f(w);
    w = g(w);
    return w;
  }
}.

equiv test : M.main ~ M.main : ={M.m,w} ==> ={M.m,res}.
fun.
eqobs_in (={M.m}) (={w}) true.
fun.
eqobs_in (={M.m}) true true.
fun.
eqobs_in (={M.m}) (={x}) true.
save.

module type Orcl = {
  fun o (x:int) : int 
}.

module type Adv (O:Orcl) = { 
  fun a1 (x:int) : int
  fun a2 (x:int) : int
}.

module O = { 
  var m : int
  fun o (x:int) : int = {
    m = x + m;
    return m;
  }
}.

module G (A:Adv) = {
  module AO = A(O)
  fun main (x:int) : int = { 
    x = AO.a1(x);
    x = O.o(x);
    x = AO.a2(x);
    return x;
  }
}.

equiv foo (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m} ==> ={res,O.m}.
fun.
eqobs_in (={O.m}) (={x}) true.
fun (={O.m}).    
 trivial.
 trivial.
fun.
 eqobs_in (={O.m}) true true.
fun.
 eqobs_in (={O.m}) true true.
fun (={O.m}).
trivial.
trivial.
fun.
eqobs_in (={O.m}) true true.
save.

equiv foo1 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,glob A} ==> ={res,O.m,glob A}.
fun.
eqobs_in (={O.m,glob A}) (={x}) true.
fun (={O.m}).    
 trivial.
 trivial.
fun.
 eqobs_in (={O.m}) true true.
fun.
 eqobs_in (={O.m,glob A}) true true.
fun (={O.m}).
trivial.
trivial.
fun.
eqobs_in (={O.m}) true true.
save.

