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

Lemma makeOnes:
  forall n,
    ones n = dropmsb (subB (shlBn (n := n.+1) #1 n) #1).
Proof.
  move=> n.
  have: toNat (ones n) = toNat (dropmsb (subB (shlBn (n := n.+1) #1 n) #1)).
    rewrite toNat_ones.
    rewrite toNat_dropmsb.
    rewrite subB1.
    rewrite toNat_decB.
    (*elim H: (shlBn #1 n == #0).*)
    have H: ~(shlBn (n := n.+1) #1 n == #0).
      by admit.
    elim H': (shlBn #1 n == #0).
      by exfalso; apply H; apply H'.
    have ->:
      (toNat (shlBn (n := n.+1) #1 n)).-1 %% 2 ^ n = (toNat (shlBn (n := n.+1) #1 n) %% 2 ^ n.+1).-1.
      by admit. (* (a -.1) %% 2 ^ n = (a %% 2 ^ n.+1) -.1 since a <> 0 *)
    rewrite toNat_shlBn.
    rewrite toNat_fromNat //.
    have ->: (2 ^ n).-1 = ((1 %% 2 ^ n.+1 * 2 ^ n) %% 2 ^ n.+1).-1.
      by admit. (* modn_small? *)
    trivial.
    trivial.
    apply toNat_inj.
Admitted.

Lemma create_repr:
  forall n (b: bool),
    create b = if b then ones n else zero n.
Proof.
  move=> n b.
  rewrite makeOnes /create fromNat0 //.
Qed.
