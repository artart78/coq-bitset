From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.
Require Import specs props.

Definition create {n} (b: bool): BITS n
  := if b then dropmsb (subB (shlBn (n := n.+1) #1 n) #1) else #0.

Lemma toNat_shlBn:
  forall n (p: BITS n) k, k < n ->
    toNat (shlBn p k) = (toNat p) * 2^k.
Proof.
  admit.
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
    rewrite toNat_shlBn.
    have H: ~(shlBn #1 n == #0).
      by admit.
    elim H': (shlBn #1 n == #0).
      admit. (* whatever *)
    rewrite toNat_fromNat //.
    have ->: div.modn (div.modn 1 (2 ^ n.+1) * 2 ^ n).-1 (2 ^ n) = (2 ^ n).-1.
      by admit.
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
