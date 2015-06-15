From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits tuple.
Require Import props.bineqs spec min.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

Lemma singleton_repr:
  forall n (k: 'I_n), repr (setBit #0 k true) [set k].
Proof.
  admit.
Admitted.

Lemma keep_min_repr:
  forall n (bs: BITS n) E x, repr bs E -> x \in E ->
    repr (andB bs (negB bs)) [set [arg min_(k < x in E) k]].
Proof.
  move=> n bs.
  have ->: andB bs (negB bs) = setBit #0 (index true bs) true.
  elim: n bs=> [bs|n IHn /tupleP[b bs]].
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
  move=> E x HE Hx.
  rewrite (index_repr n bs x E)=> //.
  apply singleton_repr.
Qed.
