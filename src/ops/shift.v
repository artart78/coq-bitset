From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun.
From MathComp
     Require Import tuple finset.
From Bits
     Require Import bits.
Require Import spec.

Lemma getBit_joinlsb:
  forall n (bs: BITS n) i b, i > 0 -> getBit (joinlsb (bs, b)) i = getBit bs (i.-1).
Proof.
  by move=> n bs; elim.
Qed.

Lemma sl_repr:
  forall n (bs: BITS n) E (H: n.-1.+1 = n), repr bs E ->
    repr (shlBn bs 1) [set i : 'I_n | 0 < i & cast_ord H (@inord n.-1 i.-1) \in E].
Proof.
  move=> n bs E H HE.
  rewrite /repr -setP /eq_mem=> i.
  rewrite !in_set.
  rewrite /shlBn /iter.
  rewrite /shlB getBit_dropmsb.
  rewrite /shlBaux.
  case Hi: (i == cast_ord H ord0).
  + (* i == 0 *)
    move/eqP: Hi=> Hi.
    rewrite Hi /=.
    by rewrite /getBit /=.
  + (* i > 0 *)
    apply negbT in Hi.
    have gtz_i: i > 0 by rewrite lt0n.
    rewrite getBit_joinlsb gtz_i=> //.
    rewrite andbC andbT.
    rewrite /repr in HE.
    move/setP: HE=> HE.
    rewrite /eq_mem in HE.
    move: (HE (cast_ord H (inord i.-1)))=> HEi.
    have {2}->: i.-1 = cast_ord H (inord i.-1).
      rewrite nat_cast_ord inordK // H.
      apply (leq_ltn_trans (n := i)).
      exact: leq_pred.
      exact: ltn_ord.
    by rewrite in_set in HEi.
    apply ltn_ord.
Qed.

Lemma sr_repr:
  forall n (bs: BITS n) E (H: n.-1.+1 = n), repr bs E ->
    repr (shrBn bs 1) [set i : 'I_n | i < n.-1 & cast_ord H (@inord n.-1 i.+1) \in E].
Proof.
  move=> n bs E H HE.
  rewrite /repr -setP /eq_mem=> i.
  rewrite !in_set /shrBn /=.
  elim: n bs E H HE i=> [//=|n IHn] /tupleP [b bs] E H HE i.
  rewrite /shrB.
  rewrite getBit_joinmsb /droplsb /splitlsb.
  rewrite tuple.beheadCons tuple.theadCons.
  rewrite /repr in HE.
  rewrite HE in_set.
  rewrite {1}succnK.
  case ltn_i: (i < n).
  + (* i < n *)
    rewrite andbC andbT.
    have ->: nat_of_ord (cast_ord H (inord i.+1)) = i.+1.
      by rewrite nat_cast_ord inordK.
    by compute.
  + (* i >= n *)
    rewrite andbC andbF /=.
    apply negbT in ltn_i.
    rewrite -leqNgt in ltn_i.
    rewrite /getBit nth_default //.
    rewrite size_tuple=> //.
  by rewrite -ltnS ltn_ord.
Qed.
