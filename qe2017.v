From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.

Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.
Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.
Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.
Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros. unfold t_empty. easy.
Qed.
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <- eqb_string_refl. easy. 
Qed.
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v Hneq. unfold t_update. rewrite false_eqb_string; easy.
Qed.
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2. apply functional_extensionality. intros xarg.
  unfold t_update. destruct (eqb_string x xarg). - easy. - easy.
Qed.
Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y. apply iff_reflect. rewrite eqb_string_true_iff. easy.
Qed.
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality. intros xarg.
  unfold t_update. destruct (eqb_stringP x xarg).
    + rewrite e. easy.
    + easy.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 Hneq. apply functional_extensionality. intros xarg.
  unfold t_update. destruct (eqb_stringP x1 xarg).
  - rewrite <- e. destruct (eqb_stringP x2 x1).
    + unfold not in Hneq. apply Hneq in e0. destruct e0.
    + easy.
  - easy.
Qed.

Definition State := (total_map nat).

(* Given part of exam, look below for answers. *)

Inductive AExp1 : Type :=
  | AN (n : nat)
  | AX (x : string)
  | AAdd (e1 e2 : AExp1)
  | AAss (x : string) (e : AExp1)
.


Inductive OS1 : AExp1 -> State -> nat -> State -> Prop :=
  | OS1_Num (n : nat) (s : State)
    : OS1 (AN n) s n s
  | OS1_Var (x : string) (s : State) (n : nat)
                         (H : (s x) = n)
    : OS1 (AX x) s n s
  | OS1_Asgn (x : string) (e : AExp1) (n : nat) (s s' : State)
                          (H : OS1 e s n s')
    : OS1 (AAss x e) s 1 (t_update s' x n)
  | OS1_Add (e1 e2 : AExp1) (s s1 s2 : State) (n n1 n2 : nat)
            (H1: OS1 e1 s n1 s1) (H2: OS1 e2 s1 n2 s2)
            (HAdd : n = (n1 + n2))
    : OS1 (AAdd e1 e2) s n s2
.


(* Question 1 *)

Definition Z := nat.
Definition Var := string.

Inductive AExp : Type :=
  | A_N (n : Z)
  | A_V (x : Var)
  | A_Add (e1 e2 : AExp)
  | A_Ass (x : Var) (e : AExp)
  | A_Fail
  | A_Otherwise (e1 e2 : AExp)
.

Inductive Return : Type :=
  | Good (z : Z) (s : State)
  | Abort
.


Inductive OS : AExp -> State -> Return -> Prop :=
  | OS_Num (n : Z) (s : State)
    : OS (A_N n) s (Good n s)
  | OS_Var (x : Var) (s : State) (n : Z)
                         (H : (s x) = n)
    : OS (A_V x) s (Good n s)
  | OS_Asgn (x : Var) (e : AExp) (n : Z) (s s' : State)
                          (H : OS e s (Good n s'))
    : OS (A_Ass x e) s (Good 1 (t_update s' x n))
  | OS_Add (e1 e2 : AExp) (s s1 s2 : State) (n n1 n2 : Z)
            (H1: OS e1 s (Good n1 s1)) (H2: OS e2 s1 (Good n2 s2))
            (HAdd : n = (n1 + n2))
    : OS (A_Add e1 e2) s (Good n s2)
  | OS_Fail (s : State)
    : OS A_Fail s Abort
  | OS_OtherwiseSafe (e1 e2 : AExp) (s s' : State) (n : Z)
            (H : OS e1 s (Good n s'))
    : OS (A_Otherwise e1 e2) s (Good n s')
  | OS_OtherwiseAbrt (e1 e2 : AExp) (s : State) (r : Return)
            (H1 : OS e1 s Abort) (H2 : OS e2 s r)
    : OS (A_Otherwise e1 e2) s r
  | OS_AddLeftAbrt (e1 e2 : AExp) (s : State)
            (H : OS e1 s Abort)
    : OS (A_Add e1 e2) s Abort
  | OS_AddRightAbrt (e1 e2 : AExp) (s s' : State) (n : Z)
            (H : OS e1 s (Good n s'))
            (H : OS e2 s' Abort)
    : OS (A_Add e1 e2) s Abort
  | OS_AsgnAbrt (x : Var) (e1 : AExp) (s : State)
            (H : OS e1 s Abort)
    : OS (A_Ass x e1) s Abort
.

(* Question 2 *)

Definition q2_exp := A_Add (A_Ass "b" (A_Otherwise 
                                       (A_Ass "a" (A_Add (A_N 3) A_Fail))
                                       (A_V "a")))
                           (A_V "b").

Definition q2_state : State := ("a" !-> 3 ; "b" !-> 8 ; _ !-> 0).

Definition q2 := exists z s, OS q2_exp q2_state (Good z s).

Theorem q2_answer : q2.
Proof. unfold q2. unfold q2_exp. unfold q2_state.
  exists 4. eexists.
  eapply OS_Add.
  - eapply OS_Asgn. eapply OS_OtherwiseAbrt.
    + eapply OS_AsgnAbrt. eapply OS_AddRightAbrt.
      * constructor.
      * apply OS_Fail.
    + apply OS_Var. easy.
  - apply OS_Var. easy.
  - constructor. 
Qed.































