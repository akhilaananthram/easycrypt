require import Int.
require import Real.
require import FMap.
require import FSet.
require CyclicGroup.

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

clone export CyclicGroup as G.

(** Construction: a PKE **)
type pkey       = G.group * G.group.
type skey       = F.t * F.t.
type plaintext  = G.group * G.group.
type ciphertext = G.group * G.group * G.group.

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
    return (g ^ r, pk1^r * m1, pk2^r * m2);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gr, gm1, gm2, sk1, sk2;
    (sk1, sk2) = sk;

    (gr, gm1, gm2) = c;
    return Some ((gm1 * gr^(-sk1),gm2 * gr^(-sk2)));
  }
}.

(** Correctness of the scheme *)

hoare Correctness: Correctness(TwoElGamal).main: true ==> res.
(* proc - get the body of the function *)
(* inline - expands function *)
(* wp - weakest precondition. fewest assumptions you need about the program to acheive the post condition *)
(* rnd - trying to equate the two probabilities from left and right by changing distribution of sampling with bijection *)
(* auto = wp. rnd. repeated *)
(* progress - simplify logic goal *)
(* algebra - simplify algebra totolagies *)
proof. 
proc.
inline*.
auto.
progress.
algebra.
qed.

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
