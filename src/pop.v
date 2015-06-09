From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div.
From Bits
     Require Import bits.
Require Import props.

(** Recursive algorithm **)

(*

(* Turns off the leftmost bit in a bitvector. *)
Fixpoint off_r_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (off_r_seq xs)
    | cons true xs => cons false xs
  end.

Lemma off_rP {n}(t: BITS n): size (off_r_seq t) == n.
Proof.
  elim: n t=> [t|n IH /tupleP [b t]] //=.
  - (* Case: n ~ 0 *)
    by rewrite (tuple0 t).
  - (* Case: n ~ n.+1 *)
    case: b=> //=.
    + (* Case: b ~ true *)
      by rewrite size_tuple.
    + (* Case: b ~ false *)
      move/eqP: (IH t) => -> //=.
Qed.

Canonical off_r {n} (t: BITS n): BITS n
  := Tuple (off_rP t).

Lemma off_r_repr:
  forall n (bs: BITS n),
    andB bs (subB bs #1) = off_r bs.
Proof.
  elim=> [bs|n IHn /tupleP [b bs]].
  - (* Case: x ~ [tuple] *)
    by apply trivialBits.
  - (* Case: x ~ [tuple b & bs] *)
    case: b.
    + (* Case: b ~ true *)
      have ->: off_r [tuple of true :: bs] = [tuple of false :: bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons
                 /andB liftBinOpCons -/andB andBB.
    + (* Case: b ~ false *)
      have ->: off_r [tuple of false :: bs] = [tuple of false :: off_r bs]
        by apply: val_inj.
      by rewrite subB1 /= tuple.beheadCons -subB1
                 /andB liftBinOpCons -/andB IHn.
Qed.

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

Definition pop_elem {n}(k: nat)(bs: BITS n)(i: nat): nat
  := let x := andB (shrBn bs (i * 2^k)) (decB (shrBn #1 (2^k))) in
     nth 0 (pop_table (2^k)) (toNat x).

Fixpoint popAux {n}(k: nat)(bs: BITS n)(i: nat): nat :=
  match i with
  | 0 => 0
  | i'.+1 => (pop_elem k bs i') + (popAux k bs i')
  end.

Definition pop {n}(k: nat)(bs: BITS n): nat
  := popAux k bs (n %/ 2^k).

Lemma pop_elem_repr:
  forall n k i (bs: BITS n)(q: n = i.+1 * 2 ^ k + (n - i.+1 * 2 ^ k))(q': i.+1 * 2 ^ k = i * 2 ^ k + 2 ^ k),
    pop_elem k bs i = count_mem true (high (2 ^ k) (tcast q' (low (i.+1 * 2 ^ k) (tcast q bs)))).
Proof.
  admit.
Admitted.

Lemma pop_rec:
  forall n k i (bs: BITS n)(q: n = i * 2 ^ k + (n - i * 2 ^ k)),
    popAux k bs i = count_mem true (low (i * (2 ^ k)) (tcast q bs)).
Proof.
  move=> n k i.
  move: i n.
  elim=> [|i IHi] n bs q.
  + (* i ~ 0 *)
    by rewrite /=.
  + (* i ~ i.+1 *)
    rewrite /popAux.
    rewrite -/popAux.
    rewrite IHi.
    admit. (* trivial equation *)
    move=> H0.
    rewrite pop_elem_repr.
    admit. (* trivial equation *)
    move=> H1.
    have H2: i * 2 ^ k + 2 ^ k = i.+1 * 2 ^ k. by admit. (* trivial *)
    have {2}->: low (i.+1 * 2 ^ k) (tcast q bs)
    = tcast H2 (high (2 ^ k) (tcast H1 (low (i.+1 * 2 ^ k) (tcast q bs))) ## low (i * 2 ^ k) (tcast H0 bs)).
      by admit.
    rewrite -count_cat.
    have ->: high (2 ^ k) (tcast H1 (low (i.+1 * 2 ^ k) (tcast q bs))) ++ low (i * 2 ^ k) (tcast H0 bs) = tcast H2
        (high (2 ^ k) (tcast H1 (low (i.+1 * 2 ^ k) (tcast q bs)))
            ## low (i * 2 ^ k) (tcast H0 bs)).
      by admit.
    by rewrite //.
Admitted.

Lemma pop_repr:
  forall n k (bs: BITS n), 2 ^ k %| n ->
    pop k bs = count_mem true bs.
Proof.
  move=> n k bs div_2k_n.
  rewrite /pop pop_rec.
  rewrite divnK.
  rewrite subnKC //.
  assumption.
  move=> H0.
  have H1: n = n %/ 2 ^ k * 2 ^ k. by admit.
  have ->: low (n %/ 2 ^ k * 2 ^ k) (tcast H0 bs) = tcast H1 bs.
    by admit.
  have ->: count_mem true bs = count_mem true (tcast H1 bs).
    by admit.
  rewrite //.
Admitted.
