
From Coq Require Import Lia.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AMul (n1 n2 : aexp)
  | AIf (nc nt nf : aexp).

(* Coercion ANum : nat >-> aexp. *)

(* Small Step aeval (provided by QE) *)
Inductive aevalS : aexp -> aexp -> Prop :=
  | Mult (n1 n2 n : nat) (H : n = n1 * n2)
    : aevalS (AMul (ANum n1) (ANum n2)) (ANum n)
  | Left0 (n : nat) 
    : aevalS (AMul (ANum 0) (ANum n)) (ANum 0)
  | Right0 (n : nat) 
    : aevalS (AMul (ANum n) (ANum 0)) (ANum 0)
  | Left (e1 e2 e1' : aexp) (H : aevalS e1 e1')
    : aevalS (AMul e1 e2) (AMul e1' e2)
  | Right (e1 e2 e2' : aexp) (H : aevalS e2 e2')
    : aevalS (AMul e1 e2) (AMul e1 e2')
  | Cond (e0 e1 e2 e0' : aexp) (H : aevalS e0 e0')
    : aevalS (AIf e0 e1 e2) (AIf e0' e1 e2)
  | CondZ (e1 e2 : aexp) (n : nat) (H : n = 0)
    : aevalS (AIf (ANum n) e1 e2) e2
  | CondNZ (e1 e2 : aexp) (n : nat) (H : n <> 0)
    : aevalS (AIf (ANum n) e1 e2) e1
.

(* Big Step aeval (Question 1) *)
(* Does it matter that im not covering the 0*n/n*0 case?
    I feel like its needless in big-step. *)
Inductive aevalB : aexp -> nat -> Prop :=
  | BNum (n : nat) 
    : aevalB (ANum n) n
  | BMult (e1 e2 : aexp) (n1 n2 n : nat) (H1 : aevalB e1 n1)
                                         (H2 : aevalB e2 n2)
                                         (H : n = n1 * n2)
    : aevalB (AMul e1 e2) n
  | BIfZ (e0 e1 e2 : aexp) (n0 n2 : nat) (H0 : aevalB e0 n0)
                                         (H2 : aevalB e2 n2)
                                         (H : n0 = 0)
    : aevalB (AIf e0 e1 e2) n2
  | BIfNZ (e0 e1 e2 : aexp) (n0 n1 : nat) (H0 : aevalB e0 n0)
                                          (H1 : aevalB e1 n1)
                                          (H : n0 <> 0)
    : aevalB (AIf e0 e1 e2) n1
.

(* Question 2 *)
(* Didnt use eapply to emphasize whats happening *)
Definition q2 := exists z, 
  aevalB (AIf (AMul (ANum 5) (ANum 0)) 
              (AMul (ANum 2) (ANum 6))
              (AMul (AMul (ANum 7) (ANum 3)) (ANum 4)))
         z.

Example q2_answer : q2.
Proof.
  unfold q2.
  exists 84.
  apply BIfZ with 0.
  - apply BMult with 5 0. + apply BNum. + apply BNum.
    + easy.
  - apply BMult with 21 4.
    + apply BMult with 7 3. * apply BNum. * apply BNum. * easy.
    + apply BNum.
    + easy.
  - easy.
Qed.

(* q2 proof but using the eapply tactic.*)
Example q2_eapply : q2.
Proof.
  unfold q2.
  exists 84.
  eapply BIfZ.
  - eapply BMult. + apply BNum. + apply BNum. + easy.
  - eapply BMult.
    + eapply BMult. * apply BNum. * apply BNum. * easy.
    + apply BNum.
    + easy.
  - easy.
Qed.

Fixpoint size (e : aexp) : nat :=
  match e with
  | ANum _ => 0
  | AMul e1 e2 => (size e1) + (size e2) + 1
  | AIf e0 e1 e2 => (size e0) + (size e1) + (size e2) + 1
  end.

(* Question 3 *)
Theorem q3_answer : 
  forall (e e' : aexp), aevalS e e' -> (size e) > (size e').
Proof.
  intros. induction H(*; simpl; lia*).
  (* size (n1 * n2) > size n *)
  - simpl. lia.
  (* size 0 * n > size 0 *)
  - simpl. lia.
  (* size n * 0 > size 0 *)
  - simpl. lia.
  (* size e1 * e2 > size e1' * e2 where e1 -> e1' *)
  - simpl. lia.
  (* size e1 * e2 > size e1 * e2' where e2 -> e2' *)
  - simpl. lia.
  (* size (e0?e1:e2) > size (e0'?e1:e2) where e0 -> e0' *)
  - simpl. lia.
  (* size (0?e1:e2) > size e2 *)
  - simpl. lia.
  (* size (n?e1:e2) > e1 where n<>0 *)
  - simpl. lia.
  (* ez answer *)
Qed.

(* Question 4 *)
(*
The size of an expression provides an upper bound on the
amount of computations required to evaluate the expression.

If evaluation of an expression is monotonically decreasing
then the size is finite. Therefore, there is always an
amount of computations required to compute the expression,
meaning that it is guaranteed to terminate.
*)




















