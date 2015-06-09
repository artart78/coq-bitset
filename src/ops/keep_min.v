From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits tuple.
Require Import props.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

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
