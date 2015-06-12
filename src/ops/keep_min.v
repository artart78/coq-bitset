From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits tuple.
Require Import props.bineqs spec.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

Lemma keep_min_repr:
  forall n (bs: BITS n) E x, repr bs E -> x \in E ->
    repr (andB bs (negB bs)) [set [arg min_(k < x in E) k]].
Proof.
  elim=> [bs|n IHn /tupleP[b bs]] E x HE Hx.
  + (* bs ~ [tuple] *)
    exfalso.
    have H: E = set0.
      admit.
    rewrite H in Hx.
    by rewrite in_set0 in Hx=> //.
  + (* bs ~ [tuple of b :: bs] *)
    case: b HE=> HE.
    - (* b ~ true *)
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbT.
      rewrite -/andB -/invB.
      rewrite andB_invB.
      rewrite /repr.
      rewrite -setP /eq_mem=> i.
      rewrite !in_set.
      case: arg_minP=> //.
      move=> i' Hi' Hj.
      have ->: getBit (consB true (zero n)) i = (i == ord0).
        by admit.
      have H': i' <= ord0 (n' := n).
        apply (Hj ord0).
        rewrite HE.
        by rewrite in_set.
      have ->: i' = ord0.
        have H: i' == ord0.
          admit.
        apply/eqP: H.
      by rewrite //.
    - (* b ~ false *)
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbF.
      rewrite -/andB -/invB -/incB.
      rewrite /repr -setP /eq_mem=> i.
      rewrite !in_set.
      by admit. (* i = 0 is trivial, i > 0 is solved using repr_rec + IHn *)
Admitted.
