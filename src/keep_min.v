From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits tuple.
Require Import specs props.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

Lemma andB_invB:
  forall n (bs: BITS n),
    andB bs (invB bs) = zero n.
Proof.
  move=> n bs.
  apply allBitsEq.
  move=> k le_k.
  rewrite getBit_liftBinOp; last by assumption.
  rewrite getBit_liftUnOp; last by assumption.
  rewrite andbN -fromNat0 getBit_zero //.
Qed.

Lemma keep_min_repr:
  forall n (bs: BITS n),
    andB bs (negB bs) = setBit #0 (index true bs) true.
Proof.
  elim=> [bs|n IHn /tupleP[b bs]].
  + (* bs ~ [tuple] *)
    by rewrite tuple0.
  + (* bs ~ [tuple of b :: bs] *)
    case: b.
    - (* b ~ true *)
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbT.
      rewrite -/andB -/invB.
      rewrite andB_invB.
      rewrite tuple.beheadCons /=.
      by rewrite fromNat0 //.
    - (* b ~ false *)
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbF.
      rewrite -/andB -/invB -/incB -/negB.
      rewrite IHn.
      by rewrite tuple.theadCons tuple.beheadCons //=.
Qed.
