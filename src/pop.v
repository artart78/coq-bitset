From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div.
From Bits
     Require Import bits.
Require Import specs props off_r.

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

(*
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
(*
Definition pop_mask_seq {n}(k: nat): seq bool
  := let fix aux n (k: 'I_k) b :=
       match n with
       | 0 => [::]
       | n'.+1 =>
         let b' := (if k == 0 then ~~ b else b) in
         cons b' (aux n' k.+1 b')
       end
     in aux n 0 false.

  match xs with
    | [::] => [::]
    | cons false xs => cons false (off_r_seq xs)
    | cons true xs => cons false xs
  end.
*)

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

Definition pop {n}(bs: BITS (2^n)): nat
  := let fix pop_count n k x :=
       match n with
       | 0 => x
       | n'.+1 => let x' := addB (andB x (pop_mask k)) (andB (shrBn x k) (pop_mask k)) in
                  pop_count n' k.*2 x'
       end
     in toNat(pop_count n 1 bs).

Fixpoint sum_tuple_seq {n}(bs: BITS n)(k: nat): seq nat
  := let fix aux n k x: seq nat :=
       match n with
       | 0 => map (fun b => (if b then 1 else 0)) bs
       | n'.+1 => let t' := aux n' (k./2) x in
                  mkseq (fun i => nth 0 t' (2 * i) + nth 0 t' (2 * i + 1)) (n %/ k)
       end
     in aux n k bs.

Lemma sum_tupleP {n}(bs: BITS n)(k: nat):
  size (sum_tuple_seq bs k) == n %/ k.
Proof.
  case: n bs=> [|n] bs.
  + (* n ~ 0 *)
    rewrite tuple0 div0n //.
  + (* n ~ n.+1 *)
    by rewrite size_mkseq //.
Qed.

Canonical sum_tuple {n}(bs: BITS n)(k: nat): (n %/ k).-tuple nat
  := Tuple (sum_tupleP bs k).

(* TODO:
 * - show that sumn (sum_tuple (pop_count n k x) k) is invariant
 * - show that sumn (sum_tuple (pop_count n k x) k) = count_mem true bs
     -> sumn (sum_tuple (pop_count n 1 bs) 1) = count_mem true bs
 *)

(* IH: the sum of the numbers representing the groups of size k
 * in (pop_count n k x) is count_mem true bs
 *)

(*
Lemma pop_repr:
  forall n (bs: BITS (2 ^ n)),
    pop bs = count_mem true bs.
Proof.
  move=> n bs.
  rewrite /pop.
*)