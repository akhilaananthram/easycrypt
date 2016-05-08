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


section.

  declare module A:TwoDDH.Adversary.

  local lemma cpa_twoddh0 &m:
      Pr[DDH0(DDHAdv(A)).main() @ &m : res] =
      Pr[DDH1(DDHAdv(A)).main() @ &m : res].
  proof.
    (* byequiv - used to move between equivalence of probability of two games to equivalence of two games *)
    (* // - discharge trivial goals; try done *)
    (* swap{A} i j - gets the games to be in sync; move line i in game A by j *)
    (* call(invariant) - expands post condition with the invariant *)
    byequiv => //;proc;inline *.
    swap{1} 7 -5.
    auto;call (_:true);auto;call (_:true);auto;progress;smt.
  qed.

  local module Gb = {
    proc main () : bool = {
      var r, x, y, z1, z2, m0, m1, b, b';
      r  = $FDistr.dt;
      x  = $FDistr.dt;
      y  = $FDistr.dt;
      (m0,m1) = A.choose(g^x);
      z1  = $FDistr.dt;
      z2 = $FDistr.dt;
      b' = A.guess(gr, gz1, gz2);
      b  = ${0,1};
      return b' = b;
    }
  }.

  local lemma ddh1_gb &m:
      Pr[TwoDDH1(TwoDDHAdv(A)).main() @ &m : res] =
      Pr[Gb.main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 3 2;swap{1} [5..6] 2;swap{2} 6 -2.
    auto;call (_:true);wp.
    rnd (fun z, z + log(if b then m1 else m0){2})
        (fun z, z - log(if b then m1 else m0){2}).
    auto;call (_:true);auto;progress; (algebra || smt).
  qed.

  (* need to assume adverary is lossless *)
  axiom Ac_l : islossless A.choose.
  axiom Ag_l : islossless A.guess.

  local lemma Gb_half &m:
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
    byphoare => //;proc.
    rnd  ((=) b')=> //=.
    call Ag_l;auto;call Ac_l;auto;progress;smt.
  qed.

  lemma conclusion &m :
    `| Pr[CPA(TwoElGamal,A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[TwoDDH0(TwoDDHAdv(A)).main() @ &m : res] -
         Pr[TwoDDH1(TwoDDHAdv(A)).main() @ &m : res] |.
  proof.
  (* rewrite - takes a lemma *)
   by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  qed.

end section.

print conclusion.
