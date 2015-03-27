From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple fintype ssrfun.
From Bits
     Require Import bits.

(* TODO: write INSTALL *)

(* This file must be read from the end. Scroll down. *)

(** 4) World domination. *)

(** 3) In x86proved, implement a bitset and bitvector library. *)

(** 2) In Coq-native, implement an efficient representation for 'BITS
n', using native (persistent) arrays and native Int63. Relate the two
using Dénès et al. refinements. *)

(** 1') Support 'blit', 'sub', 'append' and 'fill'! *)

(** 1) To formalize the operations of a 32/64bits bitset, we shall
       need operations such as: *)

Section Bitset.
  Variable n: nat.
  Variable bs bs1 bs2: BITS n.

  Definition admitted {X}: X. admit. Qed.

  Conjecture set_true_repr:
    forall (k: 'I_n),
      orB bs (shlBn #1 k) = setBit bs k true.
  Conjecture set_false_repr:
    forall (k: 'I_n),
      andB bs (negB (shlBn #1 k)) = setBit bs k false.

  (* Number of trailing zeros *)
  Conjecture ntz: BITS n -> BITS n.
  Conjecture ntz_repr: 
    ntz bs = admitted.

  (* Iterator *)
  Conjecture iteri: 
    forall A,
      BITS n -> (BITS n -> A -> A) -> A -> A.
  Conjecture iteri_repr: admitted.
  
  Conjecture left_on_repr:
    andB bs (subB #0 bs) = admitted.
  Conjecture off_mask:
    forall (k: 'I_n),
      subB bs (setBit #0 k true) = admitted.

  (* Population count/cardinal *)
  Conjecture pop: BITS n -> BITS n.
  Conjecture pop_repr: 
    pop bs = admitted.
  (* ... *)

  Conjecture inter_repr:
    forall (k: 'I_n),
      tnth (andB bs1 bs2) k = getBit bs1 k && getBit bs1 k.
  Conjecture union_repr:
    forall (k: 'I_n),
      tnth (orB bs1 bs2) k = tnth bs1 k || tnth bs1 k.
  Conjecture compl_repr: 
    forall (k: 'I_n),
      tnth (negB bs) k = negb (tnth bs k).
  Conjecture diag_repr:
    forall (k: 'I_n),
      tnth (xorB bs1 bs2) k = xorb (tnth bs1 k) (tnth bs2 k).
  (* ... *)

End Bitset.
  

(** * What's next? *)

(** SSR: as often in Coq and idiomatic in Ssreflect, even though our
specification deals with tuples of booleans, we do not write a
dependently-typed function. *)

(** Instead, we write the desired functions on lists. *)
Fixpoint off_r_seq (xs: seq bool): seq bool :=
  match xs with
    | [::] => [::]
    | cons false xs => cons false (off_r_seq xs)
    | cons true xs => cons false xs
  end.

(** We then prove some invariant on the size of the resulting list. *)
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
  
(** We conclude with a canonical structure lifting the list-level
operation to (dependently-typed) tuples. *)
Canonical off_r {n} (t: BITS n): BITS n
  := Tuple (off_rP t).


(** 

  This example turns off the leftmost bit in a bitvector. This is
  trivial to prove, but (slightly) less so to specify: we must write a
  genuine program over the list of bits.

 *)

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
      (* SSR: 'val_inj' is awfully useful for operations that are
      defined on simply-typed structures (here, 'seq bool') and that
      are lifted to dependently-typed ones (here, 'n.-tuples bool')
      through a canonical structure. The dependently-typed
      implementation does not compute: we must go through the untyped
      one. *)
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

(** * Tricky spec, simple proof *)


Lemma shrBn_Sn : 
  forall n b (bs: BITS n) k,
    shrBn [tuple of b :: bs] k.+1 = shrBn (joinmsb0 bs) k.
Proof.
  move=> n b S k.
  by rewrite {1}/shrBn iterSr //= /droplsb //= tuple.beheadCons. 
Qed.

Lemma shrB_joinmsb0:
  forall n (bs: BITS n),
    shrB (joinmsb0 bs) = joinmsb0 (shrB bs).
Proof.
  case=> [bs|n /tupleP [b bs]].
  - (* Case: n ~ 0 *)
    by rewrite tuple0.
  - (* Case: n ~ n.+1 *)
    rewrite /shrB; apply f_equal.
    have ->: droplsb [tuple of b :: bs] = bs
      by rewrite /droplsb/splitlsb //= tuple.beheadCons.
    have ->: joinmsb0 [tuple of b :: bs] = [tuple of b :: joinmsb0 bs]
      by rewrite /joinmsb0 //= tuple.theadCons tuple.beheadCons.
    by rewrite /droplsb //= tuple.beheadCons.
Qed.

Lemma shrBn_joinmsb0:
  forall n (bs: BITS n) k,
    shrBn (joinmsb0 bs) k = joinmsb0 (shrBn bs k).
Proof.
  move=> n bs.
  elim=> [|k IHk].
  - (* Case: k ~ 0 *)
    by trivial.
  - (* Case: k ~ k.+1 *)
    (* SSR: to select an occurence (here, the first) for a rewrite
    rule, we use '{n}' *)
    (* SSR: Coq is here unable to fold 'shrBn' back (with
    '-/shrBn'). We help it by giving the desired term (as a pattern)
    'shrBn _ _' and the pattern 'iter _ _ _' in the goal to which it
    reduces to. *)
    rewrite {1}/shrBn iterS -[iter _ _ _]/(shrBn _ _).
    by rewrite -shrB_joinmsb0 IHk.
Qed.



Lemma getBit_joinmsb :
  forall n (bs: BITS n) k,
    k <= n -> 
    getBit (joinmsb (false , bs)) k = getBit bs k.
Proof.
  elim=> [|n IHn] bs k leq_k_n.
  - (* Case: n ~ 0 *)
    rewrite leqn0 in leq_k_n.
    (* SSR: a '==' equality is a boolean equality, with which Coq
    *cannot* rewrite. Luckily, a boolean equality can be viewed as a
    propositional one through the 'eqP' view. *)
    move/eqP: leq_k_n=> H.
    rewrite H.
    Back 2.
    (* SSR: Once again, since we are not going to use H, we rewrite
       with it directly.  *)
    move/eqP: leq_k_n=> ->.
    by rewrite !tuple0.
  - (* Case: n ~ n.+1 *)
    case/tupleP: bs=> [b bs].
    case: k leq_k_n => [|k leq_k_n].
    + (* Case: k ~ 0 *)
      by trivial.
    + (* Case: k ~ k.+1 *)
      rewrite /joinmsb/splitlsb tuple.beheadCons tuple.theadCons -/joinmsb.
      rewrite /joinlsb //=.
      by apply: IHn; assumption.
Qed.



Lemma getBit_shrBn:
  forall n (bs: BITS n) (k: 'I_n),
    getBit (shrBn bs k) 0 = getBit bs k.
Proof.
  (* SSR: the tactical notation '[a b c]' and '[a | b | c]' are
  overloaded to perform product splitting and case splitting upon
  moves between goal and context. We can thus extract from an ordinal
  its number and associated proof. *)
  move=> n bs [k le_k].
  (* SSR: to perform an induction, we use 'elim'. The first argument
  is the hypothesis on which induction is performed while the
  remaining arguments are generalized (and then introduced). Thanks to
  '//', the system discards the 'n ~ 0' case as vacuously true. *)
  elim: n k bs le_k=> // n /= IHn k /tupleP[b bs] le_k.
  (* Case: n ~ n.+1 *)
  case: k le_k => [|k] le_k //.
  (* Case: k ~ k.+1 *)
  have ->: getBit [tuple of b :: bs] k.+1 = getBit bs k 
    by compute.
  (* SSR: We access the last subgoal of a tactical with 'last'. The
  first one is 'first'. *)
  rewrite shrBn_Sn shrBn_joinmsb0 /joinmsb0 getBit_joinmsb;
    last by apply leq0n.
  by rewrite IHn;
    last by rewrite -ltnS; assumption.
Qed.


(** 

  This is another instance of machine-code/high-level: bitmask with
  '1' to access the first bit.

 *)

(* TODO: Generalize #1 to any single-bit digit *)
Lemma andB_mask1:
  forall n (bs: BITS n),
    andB bs #1 = (if getBit bs 0 then #1 else #0).
Proof.
  (* SSR: 'case' will take the first type in the goal and perform a
  case analysis.*)
  case; [| move=> n]; move=> bs.
  (* SSR: We can in fact chain the case analysis and the introduction
  with a single '=>'. *)
  Back 2.
  case=> [|n] bs.
  (* SSR: Or equivalently: *)
  Back 1.
  case=> [bs|n bs].
  (* Exercise: figure out what the following does and fix the
  remaining proof accordingly. *)
  Back 1.
  case=> [bs|n /tupleP [b bs]].
  Back 2.
  (*
  move=> n bs.
  case: n bs. 
   
  case=> [bs|n /tupleP [b bs]].

  Back 2.*)
  - (* Case: n ~ 0 *)

    (* SSR: 'by' requires that a goal is solved before moving one. It
    forces scripts to fail early rather than too late. *)
    (* SSR: we can prefix a rewrite rule with a pattern '[ patt ]',
    thus allowing us to identify on which subterm one would like to
    perform the rewrite. *)
    by rewrite [bs]tuple0 tuple0.

  - (* Case: n ~ n.+1 *)

    (* SSR: a 'BITS n.+1' is effectively a 'n.+1-tuple
    bool'. Ssreflect provide a 'view' that allows us to see 'bs' in
    our context through the isomorphic presentation of a boolean 'b'
    and a 'n.-tuple bool' bs. To use it, we perform a case analysis
    through the view 'tupleP' view (indicated by '/tupleP') on
    'bs'. *)
    case/tupleP: bs.
    move=> b bs.
    Back 2.
    (* SSR: as usual, we can chain the moves *)
    case/tupleP: bs=> b bs.
    Back 1.
    (* SSR: we could also have proceeded in the other way
    direction. First, generalize 'bs' and view it as a pair on the way
    back *)
    move: bs=> /tupleP [b bs].
    (* SSR: to unfold the definition of 'andB', we write '/andB' (this
    is *not* a view). To fold it, we write '-/andB'. *)
    rewrite /andB liftBinOpCons -/andB.
    (* SSR: to normalize ('compute') during a rewrite, we use '/='. *)
    rewrite [_ && _]/= [andB _ _]/=.
    (* SSR: to use the rewriting rule 'fromNat0' several times, we
    prefix it with '!' *)
    rewrite Bool.andb_true_r !fromNat0.
    (* SSR: we declare intermediary lemmas with 'have H:', where 'H'
    is the name of the hypothesis. *)
    have H: andB bs (zero n) = (zero n).
    + (* Subgoal: *)
      by apply lift_right_zero; apply andbF.
    rewrite H.
    Back 4.
    (* SSR: in this case, since 'H' is an equality and we want use it
    once and now, we can use '->' instead of a name to perform the
    substitution immediately. *)
    have ->: andB bs (zero n) = (zero n).
    + (* Subgoal: *)
      by apply lift_right_zero; apply andbF.
    Back 3.
    (* SSR: because proofs for local hypothesis are supposed to be
    small, we should use the more compact form that strictly closes
    the subgoal. *)
    have ->: andB bs (zero n) = (zero n)
      by apply lift_right_zero; apply andbF.
    have ->: getBit [tuple of b :: bs] 0 = b
      by [].
    (* SSR: the pop (':') operator can be combined with 'case' so as
    to apply case on a given hypothesis in context. Intuitively, ':'
    first pops 'b' at the head of the goal and then 'case' takes it
    apart. *)
    case: b.
    + (* Case: b ~ true *)

      (* SSR: since '//' performs 'auto' and '/=' normalizes, it is to
      be expected that '//=' performs both. *)
      by rewrite -incB_fromNat /= tuple.beheadCons fromNat0 //=.
      Back 1.
      (* SSR: we could have dispensed it here since 'by' does the same
      before closing a goal anyway. *)
      by rewrite -incB_fromNat /= tuple.beheadCons fromNat0.

    + (* Case: b ~ false *)
      by rewrite zero_decomp.
Qed.


(** 

  At a high-level, this internship aims at relating combinations of
  machine-code operations (and, or, mul, etc.) with "high-level"
  specifications, expressed in terms of vectors of bits.

  Here is a concrete example, which is used to test membership in bit
  vectors. On the left-hand side, the "machine code". On the
  right-hand side, the specification.

 *)

Lemma getBit_repr:
  forall n (k: 'I_n)(bs: BITS n), 
    andB (shrBn bs k) #1 = (if getBit bs k then #1 else #0).
Proof.

  (* SSR: 'move' is for moving hypothesis between goal and
     context. '=>' gives the direction: from goal to context
     ('intro'). *)
  move=> n k S.

  (* SSR: To move from the context to the goal ('generalize'), use
  ':'. *)
  move: k.
  Back 1.
  (* SSR: We can also chain the moves: *)
  move: S k=> S.
  Back 1.
  (* SSR: 'rewrite' is generalized to sequence many rewrites. '//' is,
  roughtly, 'auto'. *)
  rewrite andB_mask1 getBit_shrBn //.
Qed.

(** * Simple spec, tricky proof *)

(**
  
  Outline:
    * Overall architecture
      + coq-bits 
      + coq-delights
      + Opam workflow
    * Introduction to Ssreflect & coq-bits
      + Proofs vs. specs in coq-delights
      + Tactics of Ssreflect
      + Curiosity-driven exploration of coq-bits
    * Upcoming work
    * Future work

 *)
    