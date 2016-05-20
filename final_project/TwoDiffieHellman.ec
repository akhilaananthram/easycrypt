require import FSet Int Real RealExtra StdRing StdOrder.
(*---*) import RField RealOrder.
require (*  *) Duni.
require (*  *) CyclicGroup.
require (*--*) DiffieHellman.


(** Assumption: set DDH *)
(* import DDH also imports CyclicGroup as G *)
clone import DiffieHellman as DH.
import DDH.

theory TwoDDH.

  module type Adversary = {
    proc guess(gr gx gy gz1 gz2:G.group): bool
  }.

  module TwoDDH0 (A:Adversary) = {
    proc main() : bool = {
      var b, r, x, y;
      r = $FDistr.dt;
      x = $FDistr.dt;
      y = $FDistr.dt;
      b = A.guess(g ^ r, g ^ x, g ^ y, g ^ (x*r), g ^ (y*r));
      return b;
    }
  }.

  module TwoDDH1 (A:Adversary) = {
    proc main() : bool = {
      var b, r, x, y, z1, z2;
      r = $FDistr.dt;
      x = $FDistr.dt;
      y = $FDistr.dt;
      z1 = $FDistr.dt;
      z2 = $FDistr.dt;
      b = A.guess(g ^ r, g ^ x, g ^ y, g ^ z1, g ^ z2);
      return b;
    }
  }.

end TwoDDH.

module DDHAdv(A:TwoDDH.Adversary) = {
  proc guess (gr, gx, gz) : bool = {
    (* gz = g^(rx) or g^r1 *)
    var y, b';
    y = $FDistr.dt;
    b' = A.guess(gr, gx, g ^ y, gz, gr ^ y);
    return b';
  }
}.



(* UNCOMMENT WHEN READY TO PROVE
section.

  declare module A:TwoDDH.Adversary.

  module local TwoDDH_Hybrid = {
    proc main() : bool = {
      var b, r, x, y, z1, gr, gx, gz;
      r = $FDistr.dt;
      x = $FDistr.dt;
      y = $FDistr.dt;
      z1 = $FDistr.dt;
      gr = g ^ r;
      gx = g ^ x;
      gz = g ^ z1;
      b = A.guess(gr, gx, g ^ y, gz, gr ^ y);
      return b;
    }
  }.

  local lemma twoddh0_hybrid &m:
      Pr[DDH0(DDHAdv(A)).main() @ &m : res] =
      Pr[TwoDDH_Hybrid.main() @ &m : res].
  proof.
    (* byequiv - used to move between equivalence of probability of two games to equivalence of two games *)
    (* // - discharge trivial goals; try done *)
    (* swap{A} i j - gets the games to be in sync; move line i in game A by j *)
    (* call(invariant) - expands post condition with the invariant *)
    byequiv => //.
    proc.
    inline *.
    swap{1} 6 -3.
    auto.
    call (_:true).
    auto.
    (*call (_:true);auto*)
    progress;smt.
  qed.
*)
