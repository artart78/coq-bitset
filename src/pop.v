From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div.
From Bits
     Require Import bits.
Require Import specs props off_r.

(** Recursive algorithm **)

(*
Lemma count_off_r:
  forall n (bs: BITS n), bs <> #0 ->
    count_mem true (andB bs (subB bs #1)) = (count_mem true bs) - 1.
Proof.
  move=> n bs bs_neqz.
  rewrite off_r_repr.
  elim: n bs bs_neqz=> [bs|n IHn bs] bs_neqz.
  + (* Case: n ~ 0 *)
    exfalso.
    apply bs_neqz.
    by apply trivialBits.
  + (* Case: n ~ n + 1 *)
    case/tupleP: bs bs_neqz=>b bs bs_neqz.
    case: b bs_neqz=> bs_neqz.
    - (* Case: b ~ true *)
      have ->: off_r [tuple of true :: bs] = [tuple of false :: bs]
        by apply: val_inj.
      rewrite /=.
      auto with arith.
    - (* Case: b ~ false *)
      have ->: off_r [tuple of false :: bs] = [tuple of false :: (off_r bs)]
        by apply: val_inj.
      rewrite /=.
      apply IHn.
      move=> bs_eqz.
      apply bs_neqz.
      rewrite bs_eqz //.
Qed.

Definition pop {n}(bs: BITS n): nat
  := let fix count n x :=
       if x == #0 then n
       else count (n + 1) (andB x (subB x #1))
     in count 0 bs.

Lemma pop_repr:
  forall n (bs: BITS n),
    pop bs = count_bits bs true.
Proof.
  admit.
Admitted.
*)

(** Algorithm using divide-and-conquer **)

(*
Definition pop_mask_seq {n}(k: nat): seq bool
  := let fix aux n :=
       match n with
       | 0 => [::]
       | n'.+1 => ((n' %% (2 * k)) >= k) :: aux n'
       end
     in aux n.

Lemma pop_maskP {n}(k: nat): size (pop_mask_seq (n := n) k) == n.
Proof.
  elim: n=> [|n IHn] //=.
Qed.

Canonical pop_mask {n} (k: nat): BITS n
  := Tuple (pop_maskP k).

Definition pop_nextBits {n}(bs: BITS (2^n))(k: nat) : BITS (2^n) :=
   addB (andB bs (pop_mask k)) (andB (shrBn bs k) (pop_mask k)).

Fixpoint popAux {n}(i: nat)(k: nat)(x: BITS (2^n)): BITS (2^n)
  := match i with
     | 0 => x
     | i'.+1 => popAux i' k.*2 (pop_nextBits x k)
     end.

Definition pop {n}(bs: BITS (2^n)): nat
  := toNat(popAux n 1 bs).

Fixpoint sum_tuple_seqAux {n}(bs: BITS (2^n))(k: nat): seq nat
  := match k with
     | 0 => map (fun b => (if b then 1 else 0)) bs
     | k'.+1 => let t' := sum_tuple_seqAux bs k' in
                mkseq (fun i => nth 0 t' (2 * i) + nth 0 t' (2 * i + 1)) (2 ^ (n - k))
     end.
(*
 * The i-th element of sum_tuple_seq bs k is the number of bits to 1
 * from offset i * 2^k to offset (i + 1) * 2^k
 *)
Definition sum_tuple_seq {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n): seq nat
  := sum_tuple_seqAux bs k.

Lemma sum_tupleP {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n):
  size (sum_tuple_seq bs k le_k) == 2^(n - k).
Proof.
  case: k le_k=> [|k] le_k.
  + (* k ~ 0 *)
    by rewrite size_map size_tuple subn0.
  + (* k ~ k.+1 *)
    by rewrite size_mkseq.
Qed.

Canonical sum_tuple {n}(bs: BITS (2^n))(k: nat)(le_k: k <= n): (2^(n - k)).-tuple nat
  := Tuple (sum_tupleP bs k le_k).

(*
 * sumn (sum_tuple (addB (andB x (pop_mask k)) (andB (shrBn x k) (pop_mask k))) k.*2)
 * (= sumn (sum_tuple f(x) k.*2))
 * = sumn (sum_tuple x k)

   sum_tuple x k [i.*2] + sum_tuple x k [i.*2 + 1]
   = sum_tuple f(x) k.*2 [i]

 * 1) Show that sum_tuple x k [i] = toNat (take k (shrB (k*i) x))
 * 2) Show that:
   toNat (take k (shrBn (k*i.*2) x)) + toNat (take k (shrBn (k*i.*2 + k) x)) (X)
   = toNat (take k.*2 (shrBn (k*i.*2) f(x)))

   Because (addB (take k bs) (take k bs')) = take k.*2 (addB bs bs'):
   X = toNat (take k.*2 (addB (shrBn (k*i.*2) x) (shrBn (k*i.*2 + k) x)))

   And:
   take k.*2 (shrBn (k*i.*2) (addB (andB x (pop_mask k)) (andB (shrBn x k) (pop_mask k)))
   = take k.*2 (addB (shrBn (k*i.*2) x) (shrBn (k*i.*2 + k) x))

   => sumn (sum_tuple bs 1) = sumn (sum_tuple (popAux n 1 bs) (2^n))
      = count_mem true bs     = pop bs
*)

Lemma pop_repr:
  forall n (bs: BITS (2 ^ n)),
    pop bs = count_mem true bs.
Proof.
  move=> n bs.
  have H: n <= n by trivial.
  have ->: pop bs = sumn (sum_tuple (popAux n 1 bs) n H)
    by admit.
  have H': 0 <= n by trivial.
  have ->: count_mem true bs = sumn (sum_tuple bs 0 H')
    by admit.
  have: forall x k, sumn (sum_tuple x k) = sumn (sum_tuple bs 1)
    -> sumn (sum_tuple (pop_nextBits x k) k.*2) = sumn (sum_tuple bs 1).
    admit.
    rewrite /popAux.
  admit.
Admitted.
*)

Definition pop_table (n: nat) := mkseq (fun i => count_mem true (fromNat (n := 2^n) i)) (2^n).

Definition getLsb_seq {n}(bs: BITS n)(k: nat)(le_k: k <= n): seq bool :=
  take k bs.

Lemma getLsbP {n}(bs: BITS n)(k: nat)(le_k: k <= n): size (getLsb_seq (n := n) bs k le_k) == k.
Proof.
  rewrite /getLsb_seq.
  have {2}->: k = minn k n by admit.
  apply take_tupleP.
Admitted.

Canonical getLsb {n}(bs: BITS n)(k: nat)(le_k: k <= n): BITS k
  := Tuple (getLsbP bs k le_k).

Definition pop_elem (n: nat)(bs: BITS n)(k: nat)(i: nat)(le_k: (2^k) <= n): nat
  := let x := andB (getLsb (shrBn bs (i * 2^k)) (2^k) le_k) (ones (2^k)) in
     nth 0 (pop_table (2^k)) (toNat x).

Fixpoint popAux (n: nat)(bs: BITS n)(k: nat)(i: nat)(le_k: (2^k) <= n): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem n bs k i' le_k) + (popAux n bs k i' le_k)
  end.

Definition pop {n}(bs: BITS n)(k: nat)(le_k: (2^k) <= n): nat
  := popAux n bs k (n %/ 2^k) le_k.

Lemma count_sep:
  forall x s i i', i < i' ->
  count_mem x (drop i (take i' s)) + count_mem x (take i s)
  = count_mem true (take i' s).
Proof.
  admit.
Admitted.

Lemma pop_rec:
  forall n (bs: BITS (2 ^ n)) k (le_k: 2^k <= 2^n) i,
    popAux (2 ^ n) bs k i le_k = count_mem true (take (i * (2 ^ k)) bs).
Proof.
  move=> n bs k le_k.
  elim=> [|i IHi].
  + (* i ~ 0 *)
    by rewrite mul0n take0.
  + (* i ~ i.+1 *)
    rewrite /popAux.
    rewrite -/popAux.
    rewrite IHi.
    have ->: pop_elem (2 ^ n) bs k i le_k
      = count_mem true (drop (i * (2 ^ k)) (take (i.+1 * (2 ^ k)) bs)).
      by admit.
    apply count_sep.
    rewrite ltn_pmul2r.
    rewrite ltnSn //.
    by rewrite expn_gt0 //.
Admitted.

Lemma pop_repr:
  forall n (bs: BITS (2 ^ n)) k (le_k: 2^k <= 2^n),
    pop bs k le_k = count_mem true bs.
Proof.
  move=> n bs k le_k.
  rewrite /pop pop_rec.
  rewrite take_oversize //.
  rewrite size_tuple divnK //.
  rewrite dvdn_exp2l //.
  rewrite leq_exp2l in le_k.
  assumption.
  by rewrite //.
Qed.
