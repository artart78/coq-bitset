From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun finset.
From Bits
     Require Import bits tuple.
Require Import props.bineqs props.getbit spec min.

Definition keep_min {n} (bs: BITS n): BITS n
  := andB bs (negB bs).

Lemma keep_min_repr:
  forall n (bs: BITS n) E x, repr bs E -> x \in E ->
    repr (keep_min bs) [set [arg min_(k < x in E) k]].
Proof.
  move=> n bs.
  rewrite /keep_min.
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
  rewrite (index_repr n bs x E)=> //.
  by apply singleton_repr.
Qed.
