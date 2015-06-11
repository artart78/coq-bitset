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
      by admit. (* ord0 \in E -> i' <= ord0 -> i' = ord0 *)
    - (* b ~ false *)
      rewrite /negB /incB /invB /andB /=.
      rewrite liftUnOpCons tuple.beheadCons.
      rewrite liftBinOpCons andbF.
      rewrite -/andB -/invB -/incB.
      by admit. (* Harder: we have to show a result over sets of 'I_n.+1 from a result over sets of 'I_n.
      Maybe using arg_minP & the fact that '<=' is the same for nat and ordinals is enough? *)
Admitted.
