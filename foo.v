Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.FunctionalExtensionality.

Import VectorNotations.

Section StackProof.

Variable A : Type.
Variable default : A.
Variable n : nat.
Hypothesis n_pos : n > 1.

(* Stack state record *)
Record StackState := {
  stack : t A n;
  stackIdx : nat (* invariant: stackIdx < n *)
}.

(* Safe nth with default if out of bounds *)
Definition safe_nth (v : t A n) (i : nat) : A :=
  if i <? n then nth v i else default.

(* Safe replace with no change if index out of bounds *)
Definition safe_replace (i : nat) (x : A) (v : t A n) : t A n :=
  if i <? n then replace v i x else v.

(* Stack step function *)
Definition stack_step
  (s : StackState)
  (input : option A * bool) (* (push, pop) *)
  : StackState * (option A * bool) :=
  let '(push_data, pop) := input in
  let idx := s.(stackIdx) in
  let stk := s.(stack) in
  let popped :=
    if pop && (idx <? n) then Some (safe_nth stk idx)
    else None in
  let idx' := if pop then idx - 1 else idx in
  let '(new_stk, new_idx) :=
    match push_data, (idx' + 1 <? n) with
    | Some x, true => (safe_replace (idx' + 1) x stk, idx' + 1)
    | _, _ => (stk, idx')
    end in
  let new_state := {| stack := new_stk; stackIdx := new_idx |} in
  let ready := negb (new_idx =? n - 1) in
  (new_state, (popped, ready)).

(* Invariant: stack index is always within bounds *)
Definition valid_state (s : StackState) : Prop :=
  s.(stackIdx) < n.

(* Initial state *)
Definition empty_stack : StackState :=
  {| stack := repeat default n; stackIdx := 0 |}.

Lemma valid_init : valid_state empty_stack.
Proof.
  unfold valid_state, empty_stack. simpl.
  apply n_pos.
Qed.

Lemma push_increments_index :
  forall s x,
    valid_state s ->
    s.(stackIdx) + 1 < n ->
    let (s', _) := stack_step s (Some x, false) in
    s'.(stackIdx) = S s.(stackIdx).
Proof.
  intros s x Hvalid Hbound.
  destruct s as [stk idx].
  simpl in *.
  unfold stack_step. simpl.
  rewrite Nat.eqb_neq.
  assert (Htest: (idx + 1 <? n) = true) by apply Nat.ltb_lt.
  rewrite Htest.
  simpl.
  now rewrite <- plus_n_Sm.
Qed.

Lemma pop_decrements_index :
  forall s,
    valid_state s ->
    0 < s.(stackIdx) ->
    let (s', _) := stack_step s (None, true) in
    s'.(stackIdx) = s.(stackIdx) - 1.
Proof.
  intros s Hvalid Hgt.
  destruct s as [stk idx]. simpl in *.
  unfold stack_step. simpl.
  rewrite Nat.eqb_neq.
  destruct (idx <? n) eqn:Hlt.
  - destruct (None, true). simpl.
    destruct (None) eqn:?; simpl.
    + discriminate.
    + destruct (idx - 1 + 1 <? n) eqn:?; simpl; auto.
  - apply Nat.ltb_ge in Hlt. lia.
Qed.

Lemma push_pop_roundtrip :
  forall s x,
    valid_state s ->
    s.(stackIdx) + 1 < n ->
    let (s', _) := stack_step s (Some x, false) in
    let (s'', (popped, _)) := stack_step s' (None, true) in
    popped = Some x.
Proof.
  intros s x Hvalid Hbound.
  destruct s as [stk idx]. simpl in *.
  unfold stack_step at 1.
  rewrite Nat.eqb_neq.
  assert (Hpush_idx: idx + 1 <? n = true) by apply Nat.ltb_lt.
  rewrite Hpush_idx.
  simpl.
  set (stk' := safe_replace (idx + 1) x stk).
  set (idx' := idx + 1).
  remember {| stack := stk'; stackIdx := idx' |} as s'.
  unfold stack_step at 1.
  simpl.
  rewrite Nat.eqb_neq.
  rewrite Nat.ltb_lt.
  rewrite <- Heqs'.
  unfold safe_nth, safe_replace.
  rewrite Nat.ltb_lt.
  rewrite <- Heqs'. simpl.
  destruct (idx' <? n) eqn:?.
  - apply Nat.ltb_lt in Heqb0.
    rewrite if_true by assumption.
    reflexivity.
  - exfalso.
    subst idx'. lia.
Qed.

Lemma stack_idx_within_bounds :
  forall s input s' out,
    valid_state s ->
    (s', out) = stack_step s input ->
    valid_state s'.
Proof.
  intros s [push pop] s' out Hvalid Hstep.
  destruct s as [stk idx].
  unfold stack_step in Hstep.
  simpl in *.
  destruct push as [x|]; destruct pop; simpl in *;
  destruct (idx <? n) eqn:Hlt;
  try destruct (idx - 1 + 1 <? n); inversion Hstep; subst; simpl;
  try lia;
  apply Nat.ltb_lt in Hlt; lia.
Qed.

End StackProof.

