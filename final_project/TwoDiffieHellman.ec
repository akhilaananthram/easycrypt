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

module DDHAdv(A:Adversary) = {
  proc guess (gr, gx, gz) : bool = {
    (* gz = g^(rx) or g^r1 *)
    var y, b';
    y = $FDistr.dt;
    b' = A.guess(gr, gx, g ^ y, gz, gr ^ y);
    return b';
  }
}.

(** Set version of the Computational Diffie-Hellman problem **)
theory Set_CDH.

  const n: int.

  module type Adversary = {
    proc solve(gx:group, gy:group): group fset
  }.

  module SCDH (B:Adversary) = {
    proc main(): bool = {
      var x, y, s;

      x = $FDistr.dt;
      y = $FDistr.dt;
      s = B.solve(g ^ x, g ^ y);
      return (mem s (g ^ (x * y)) /\ card s <= n);
    }
  }.

  module CDH_from_SCDH (A:Adversary): CDH.Adversary = {
    proc solve(gx:group, gy:group): group = {
      var s, x;

      s = A.solve(gx, gy);
      x = $Duni.dU s;
      return x;
    }
  }.

  (** Naive reduction to CDH **)
  section.
    declare module A: Adversary.

    local module SCDH' = {
      var x, y: F.t

      proc aux(): group fset = {
        var s;

        x = $FDistr.dt;
        y = $FDistr.dt;
        s = A.solve(g ^ x, g ^ y);
        return s;
      }

      proc main(): bool = {
        var z, s;

        s = aux();
        z = $Duni.dU s;
        return z = g ^ (x * y);
      }
    }.

    lemma Reduction &m:
      0 < n =>
      1%r / n%r * Pr[SCDH(A).main() @ &m: res]
      <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res].
    proof.
      (* Move "0 < n" into the context *)
      move=> n_pos.
      (* We prove the inequality by transitivity:
           1%r/n%r * Pr[SCDH(A).main() @ &m: res]
           <= Pr[SCDH'.main() @ &m: res]
           <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res]. *)
      (* "first last" allows us to first focus on the second inequality, which is easier. *)
      apply (ler_trans Pr[SCDH'.main() @ &m: res]); first last.
        (* Pr[SCDH'.main() @ &m: res] <= Pr[CDH.CDH(CDH_from_SCDH(A)).main() @ &m: res] *)
        (* This is in fact an equality, which we prove by program equivalence *)
        byequiv (_: _ ==> ={res})=> //=.
        by proc; inline *; auto; call (_: true); auto.
      (* 1%r/n%r * Pr[SCDH(A).main() @ &m: res] <= Pr[SCDH'.main() @ &m: res] *)
      (* We do this one using a combination of phoare (to deal with the final sampling of z)
         and equiv (to show that SCDH'.aux and CDH.CDH are equivalent in context). *)
      byphoare (_: (glob A) = (glob A){m} ==> _)=> //.
      (* This line is due to a bug in proc *) pose d:= 1%r/n%r * Pr[SCDH(A).main() @ &m: res].
      pose p:= Pr[SCDH(A).main() @ &m: res]. (* notation for ease of writing below *)
      proc.
      (* We split the probability computation into:
           - the probability that s contains g^(x*y) and that |s| <= n is Pr[SCDH(A).main() @ &m: res], and
           - when s contains g^(x*y), the probability of sampling that one element uniformly in s is bounded
             by 1/n. *)
      seq  1: (mem s (g ^ (SCDH'.x * SCDH'.y)) /\ card s <= n) p (1%r/n%r) _ 0%r => //.
        (* The first part is dealt with by equivalence with SCDH. *)
        conseq (_: _: =p). (* strengthening >= into = for simplicity*)
          call (_: (glob A) = (glob A){m}  ==> mem res (g^(SCDH'.x * SCDH'.y)) /\ card res <= n)=> //.
            bypr; progress; rewrite /p.
            byequiv (_: )=> //.
            by proc *; inline *; wp; call (_: true); auto.
      (* The second part is just arithmetic, but smt needs some help. *)
      rnd (Pred.pred1 (g^(SCDH'.x * SCDH'.y))).
      skip; progress.
        rewrite Duni.mu_dU filter_pred1 H /= fcard1.
        cut H1: 0 < card s{hr} by smt.
        by rewrite mul1r lef_pinv /#.
        smt.
    qed.
  end section.

end Set_CDH.