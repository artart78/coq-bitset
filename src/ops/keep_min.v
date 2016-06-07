Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits ssrextra.tuple.
From CoqEAL Require Import refinements.
Require Import ops spec min.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

Import Refinements.Op.

Global Instance eq_Fin {n} : eq_of 'I_n := (fun x y => x == y).

Local Instance refl_I {n} (x : 'I_n) : refines Logic.eq x x.
by rewrite refinesE //.
Qed.


Lemma keep_min_repr:
  forall n (bs: BITS n) E x, refines Rfin bs E -> x \in E ->
      Rfin (keep_min bs) (singleton_op [arg min_(k < x in E) k]).
Proof.
  move=> n bs.
  rewrite /keep_min.
  Typeclasses eauto := debug.
  
  have ->: andB bs (negB bs) = setBit #0 (index true bs) true.
  elim: n bs=> [bs|n IHn /tupleP[b bs]].
  + (* bs ~ [tuple] *)
    by rewrite tuple0.
  + (* bs ~ [tuple of b :: bs] *)
    case: b.
    - (* b ~ true *)
      by rewrite /negB /incB /invB /andB /=
                 liftUnOpCons !tuple.beheadCons liftBinOpCons andbT
                 -/andB -/invB andB_invB fromNat0.
    - (* b ~ false *)
      by rewrite /negB /incB /invB /andB /=
                 liftUnOpCons tuple.theadCons !tuple.beheadCons liftBinOpCons andbF
                 -/andB -/invB -/incB -/negB IHn.
  move=> E x HE Hx.
  rewrite refinesE in HE.
  rewrite (index_repr n bs x E)=> //.
  rewrite -[setBit _ _ _]/((fun (k : 'I_n) => setBit #0 k true) [arg min_(k < x in E) k]). 
  rewrite -[(fun k : 'I_n => setBit # (0) k true)]/(singleton_op).
  apply: refinesP.
Qed.
