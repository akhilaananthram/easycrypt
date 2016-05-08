require import Int.
require import Real.
require import FMap.
require import FSet.

(*
Useful to get groups
*)
require (*--*) TwoDiffieHellman.
(*
Scheme (module type) with 3 procedures -> key gen, enc, dec
Adversary (module type)
CPA, CCA (functor)
*)
require (*--*) PKE.

(** Assumption: set TwoDDH *)
clone import TwoDiffieHellman as TDH.
import TwoDDH.

(** Construction: a PKE **)
type pkey       = group * group.
type skey       = F.t * F.t.
type plaintext  = group * group.
type ciphertext = group * group * group.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(** Concrete Construction: ElGamal **)
module TwoElGamal : Scheme = {
  proc kg(): pkey * skey = {
    var sk1, sk2;

    sk1 = $FDistr.dt;
    sk2 = $FDistr.dt;
    return ((g ^ sk1, g ^ sk2), (sk1, sk2));
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var r, pk1, pk2, m1, m2;
    (pk1, pk2) = pk;
    (m1, m2) = m;

    r = $FDistr.dt;
    return (g ^ r, pk1^r * m1, pk2^r * m);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gr, gm1, gm2;

    (gr, gm1, gm2) = c;
    return Some ((gm1 * gr^(-sk1),gm2 * gr^(-sk2)));
  }
}.

(** Correctness of the scheme *)

hoare Correctness: Correctness(ElGamal).main: true ==> res.
(* proc - get the body of the function *)
(* inline - expands function *)
(* wp - weakest precondition. fewest assumptions you need about the program to acheive the post condition *)
(* rnd - trying to equate the two probabilities from left and right by changing distribution of sampling with bijection *)
(* auto = wp. rnd. repeated *)
(* progress - simplify logic goal *)
(* algebra - simplify algebra totolagies *)
proof. proc; inline*; auto; progress; algebra. qed.

(** Exact security *)

module TwoDDHAdv(A:Adversary) = {
  proc guess (gr, gx, gy, gz1, gz2) : bool = {
    var m0, m1, mb1, mb2, b, b';
    (m0, m1) = A.choose(gx);
    b = ${0,1};
    (mb1, mb2) = b?m1:m0;
    b' = A.guess(gr, gz1 * mb1, gz2 * mb2);
    return b' = b;
  }
}.

section Security.

  declare module A:Adversary.

  local lemma cpa_twoddh0 &m:
      Pr[CPA(TwoElGamal,A).main() @ &m : res] =
      Pr[TwoDDH0(TwoDDHAdv(A)).main() @ &m : res].
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

end section Security.

print conclusion.
