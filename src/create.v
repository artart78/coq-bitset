From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun div.
From Bits
     Require Import bits.
Require Import specs props.

Definition create {n} (b: bool): BITS n
  := if b then dropmsb (subB (shlBn (n := n.+1) #1 n) #1) else #0.

Lemma toNat_shlBn:
  forall n (p: BITS n) k, k < n ->
    (toNat (shlBn p k)) %% 2^n = ((toNat p) * 2^k) %% 2^n.
Proof.
  move=> n p k le_k.
  elim: k le_k=> [|k IHk] le_k.
  + (* Case: k ~ 0 *)
    by rewrite /shlBn expn0 muln1 /= -toNat_mod.
  + (* Case: k ~ k + 1 *)
    rewrite /shlBn.
    rewrite iterS.
    rewrite -[iter k shlB p]/(shlBn _ _).
    rewrite toNat_shlB.
    have ->: (toNat p * 2 ^ k.+1) = ((toNat p * 2 ^ k).*2).
      rewrite expnS //=.
      rewrite mulnA.
      rewrite mulnAC.
      rewrite muln2.
      by rewrite //.
    have H: (toNat (shlBn p k)) %% 2 ^ n = (toNat p * 2 ^ k) %% 2 ^ n.
      rewrite IHk //.
      auto with arith.
    admit. (* a = b %[mod n] -> a .*2 = b .*2 %[mod n] *)
Admitted.

(* TODO: merge with the lemma below *)
Lemma toNat_subB:
  forall n, n > 0 ->
    toNat (subB (shlBn (n := n.+1) #1 n) #1) = (2 ^ n) - 1.
Proof.
  move=> n.
  rewrite toNat_subB.
  have ->: toNat (n := n.+1) #1 = 1.
  rewrite toNat_fromNat.
  admit. (* 1 %% 2 ^ n.+1 = 1 *)
  have ->: toNat (shlBn (n := n.+1) #1 n) = 2 ^ n.
    by admit. (* Uses toNat_shlBn + modn_small *)
  trivial.
  admit. (* leB #1 (shlBn #1 n) *)
Admitted.

Lemma makeOnes:
  forall n, n > 0 ->
    ones n = dropmsb (subB (shlBn (n := n.+1) #1 n) #1).
Proof.
  move=> n gtz_n.
  have: toNat (ones n) = toNat (dropmsb (subB (shlBn (n := n.+1) #1 n) #1)).
    rewrite toNat_ones.
    rewrite toNat_dropmsb.
    rewrite toNat_subB.
    rewrite modn_small.
    rewrite subn1.
    trivial.
    admit. (* 2 ^ n - 1 < 2 ^ n *)
    assumption.
    apply toNat_inj.
Admitted.

Lemma create_repr:
  forall n (b: bool),
    create b = if b then ones n else zero n.
Proof.
  move=> n b.
  rewrite makeOnes /create fromNat0 //.
Qed.
