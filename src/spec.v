Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple finset.
From Bits
     Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BitRepr.

Definition repr n (bs : BITS n) E := E = [set x : 'I_n | getBit bs x].

Lemma repr_rec n (bs : BITS n) (E : {set 'I_n.+1}) b :
  repr [tuple of b :: bs] E ->
  repr bs [set x : 'I_n | inord(x.+1) \in E ].
Proof. by move->; apply/setP=> x; rewrite !inE inordK //; exact: ltn_ord. Qed.

Variable n : nat.
Implicit Types (bs : BITS n) (E: {set 'I_n}).

Lemma eq_repr bs bs' E E' : repr bs E -> repr bs' E' ->
    (bs == bs') = (E == E').
Proof.
move=> -> ->; apply/eqP/eqP => [ -> // |].
move/setP=> hs; apply: allBitsEq=> i i_ord.
by have := hs (Ordinal i_ord); rewrite !inE.
Qed.

Lemma empty_repr : repr (zero n) set0.
Proof. by apply/setP=> i; rewrite !inE -fromNat0 getBit_zero. Qed.

Lemma subset_repr k (k_le_n : k <= n) :
  repr (decB (shlBn #1 k)) [set x : 'I_n | x < k].
Proof.
rewrite makeOnes ?subnKC //= => ?.
apply/setP=> i; rewrite !inE getBit_tcast getBit_catB.
by case: ifP => h; rewrite ?getBit_ones // -fromNat0 getBit_zero.
Qed.

Lemma singleton_repr (k: 'I_n) : repr (setBit #0 k true) [set k].
Proof.
apply/setP=> i; rewrite !inE; apply/eqP/idP => [->|].
  by rewrite setBitThenGetSame.
apply: contraTeq => /eqP i_neq_k.
rewrite setBitThenGetDistinct ?ltn_ord ?getBit_zero //.
(* XXX: The impedance here should be fixed *)
by move/val_inj => h; apply: i_neq_k.
Qed.

(* XXX: I disagree with this but it is a "mal menor" for now *)
Lemma indexP (T : eqType) d (x : T) s idx :
  d != x -> nth d s idx = x ->
  (forall j, j < size s -> nth d s j = x -> idx <= j) ->
  index x s = idx.
Proof.
elim: s idx => [|s ss ihs] idx hneq; first by move/eqP: hneq; rewrite nth_nil.
case: idx => /= [->|idx]; first by rewrite eqxx.
move=> /ihs-/(_ hneq) {ihs} ihs hj.
case: ifP => [/eqP|] he; first by have /= := hj 0 erefl he; rewrite ltn0.
by congr S; apply: ihs => j hjs hnt; have := hj j.+1 hjs hnt.
Qed.

Lemma index_repr bs x E (hr : repr bs E) (h_in : x \in E) :
  index true bs = [arg min_(k < x in E) k].
Proof.
case: arg_minP => // i xin ihh.
(* XXX: I disagree with this: there is a better solution but requires
   a different library structure *)
have/indexP: nth false bs i = true.
  by have/setP:= hr => /(_ i); rewrite xin inE => ->.
apply=> // j hj hnt; rewrite size_tuple in hj.
by have:= ihh (Ordinal hj); apply; rewrite hr inE.
Qed.

(* XXX: Same than above *)
Lemma count_nth_cons x xs :
      count (nth false (x :: xs)) (iota 0 (size xs).+1) =
  x + count (nth false xs)        (iota 0 (size xs)).
Proof. by congr addn; elim: (size _) 0 => //= size ihsz z; rewrite ihsz. Qed.

Lemma count_repr bs E : repr bs E -> count_mem true bs = #|E|.
Proof.
move=> -> {E}; rewrite cardsE cardE size_filter.
rewrite -(count_map val) unlock val_ord_enum.
case: bs => s ss; elim: s n ss => /= [ | x xs ihs] m /eqP <-{m} //.
by rewrite count_nth_cons -ihs //; congr addn; case: x.
Qed.

End BitRepr.
