From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
Import ListNotations.
Open Scope string_scope.

Inductive Act : Type :=
  | Lab (n : string)
  | Special
.

Coercion Lab : string >-> Act.

Inductive Proc : Type :=
  | P0
  | PPrefix (a : Act) (p : Proc)
  | PChoice (p1 p2 : Proc)
  | PPar (p1 p2 : Proc)
  | PRestrict (p : Proc) (x : list string)
.

Inductive peval : Proc -> Act -> Proc -> Prop :=
  | Prefix (a : Act) (p : Proc)
    : peval (PPrefix a p) a p
  | Choice1 (p1 p2 : Proc)
    : peval (PChoice p1 p2) Special p1
  | Choice2 (p1 p2 : Proc)
    : peval (PChoice p1 p2) Special p2
  | Par1 (a : Act) (p1 p2 p1' : Proc) (H : peval p1 a p1')
    : peval (PPar p1 p2) a (PPar p1' p2)
  | Par2 (a : Act) (p1 p2 p2' : Proc) (H : peval p2 a p2')
    : peval (PPar p1 p2) a (PPar p1 p2')
  | Par3 (a : Act) (p1 p2 p1' p2' : Proc) (H1 : peval p1 a p1')
                                          (H2 : peval p2 a p2')
    : peval (PPar p1 p2) Special (PPar p1' p2')
  (* TODO: Idk how to represent `a NotIn x` here. *)
  | Restrict (p p' : Proc) (x : list string) (a : Act)
                                            (H : peval p a p')
    : peval (PRestrict p x) a (PRestrict p' x)
.



(* (d.a.b.0)\{d, b} *)
(* b.( *.0 + c.a.0) *)

Hint Constructors peval.

(* Question 1! *)

(* q1a *)
Definition q1a := (PChoice (PRestrict (PPrefix "d" (PPrefix "a" (PPrefix "b" P0))) 
                                          ["d" ; "b"])
                       (PPrefix "b" (PChoice (PPrefix Special P0) 
                                             (PPrefix "c" (PPrefix "a" P0))))).
Definition q1a1 := (PRestrict (PPrefix "d" (PPrefix "a" (PPrefix "b" P0))) 
                                          ["d" ; "b"]).
Definition q1a2 := (PPrefix "b" (PChoice (PPrefix Special P0) 
                                           (PPrefix "c" (PPrefix "a" P0)))).

Theorem q1a1_holds : peval q1a Special q1a1.
Proof.
  eapply Choice1.
Qed.

Theorem q1a2_holds : peval q1a Special q1a2.
Proof. eapply Choice2. Qed.

(* This proves that the only derivations for q1a
  are q1a1 and q1a2. I didnt do this for other sub-problems. *)
Theorem q1a_1_2_holds_only : forall (p : Proc) (a : Act),
  peval q1a a p -> (a = Special /\ (p = q1a1 \/ p = q1a2)).
Proof. 
  unfold q1a. unfold q1a1. unfold q1a2.
  intros. inversion H.
  - auto.
  - auto.
Qed.

(* q1b *)

Definition q1b := (PPar (PPar (PPrefix "a" (PPrefix "b" P0))
                              (PPrefix "c" (PPrefix "a" P0)))
                        (PPrefix "c" (PPrefix "b" P0))).

(* Holds with a="c" *)
Definition q1b1 := (PPar (PPar (PPrefix "a" (PPrefix "b" P0)) 
                               (PPrefix "c" (PPrefix "a" P0))) 
                          (PPrefix "b" P0)).
(* Holds with a="a" *)
Definition q1b2 := (PPar (PPar (PPrefix "b" P0) 
                               (PPrefix "c" (PPrefix "a" P0))) 
                         (PPrefix "c" (PPrefix "b" P0))).
(* Holds with a="c" *)
Definition q1b3 := (PPar (PPar (PPrefix "a" (PPrefix "b" P0)) 
                               (PPrefix "a" P0)) 
                          (PPrefix "c" (PPrefix "b" P0))).
(* Holds with a=Special *)
Definition q1b4 := (PPar (PPar (PPrefix "a" (PPrefix "b" P0))
                               (PPrefix "a" P0))
                         (PPrefix "b" P0)).

Theorem q1b1_holds : peval q1b "c" q1b1.
Proof. eapply Par2. eapply Prefix. Qed.

Theorem q1b2_holds : peval q1b "a" q1b2.
Proof. eapply Par1. eapply Par1. eapply Prefix. Qed.

Theorem q1b3_holds : peval q1b "c" q1b3.
Proof. eapply Par1. eapply Par2. eapply Prefix. Qed.

Theorem q1b4_holds : peval q1b Special q1b4.
Proof. eapply Par3. eapply Par2. eapply Prefix. eapply Prefix.
Qed.


(* q1c *)

Definition q1c := PPar (PPar (PChoice (PPrefix "a" P0) 
                                      (PPrefix "b" P0))
                             (PPrefix "c" P0))
                       (PPrefix "e" P0).

(* Proven with Par2 -> Prefix "e" *)
Definition q1c1 := PPar (PPar (PChoice (PPrefix "a" P0) 
                                       (PPrefix "b" P0))
                        (PPrefix "c" P0))
                       P0.

(* Proven with  Par1 -> Par2 -> Prefix "c"*)
Definition q1c2 := PPar (PPar (PChoice (PPrefix "a" P0) 
                                       (PPrefix "b" P0))
                              P0)
                        (PPrefix "e" P0).

(* Proven with Par1 -> Par1 -> Choice1 *)
Definition q1c3 := PPar (PPar (PPrefix "a" P0)
                              (PPrefix "c" P0))
                        (PPrefix "e" P0).

(* Proven with Par1 -> Par1 -> Choice2 *)
Definition q1c4 := PPar (PPar (PPrefix "b" P0)
                              (PPrefix "c" P0))
                        (PPrefix "e" P0).

Theorem q1c1_holds : peval q1c "e" q1c1.
Proof.  
  eapply Par2. eapply Prefix. 
Qed.

Theorem q1c2_holds : peval q1c "c" q1c2.
Proof. eapply Par1. eapply Par2. apply Prefix.  Qed.

Theorem q1c3_holds : peval q1c Special q1c3.
Proof. eapply Par1. eapply Par1. eapply Choice1. Qed.

Theorem q1c4_holds : peval q1c Special q1c4.
Proof. eapply Par1. eapply Par1. eapply Choice2. Qed.



(* q1d *)

Definition q1d := PRestrict (PPar (PPar (PPrefix "b" 
                                                 (PPrefix "c" P0))
                                        (PPrefix "a"
                                                 (PPrefix "d" P0)))
                                  (PPrefix "b" P0))
                            ["b" ; "c"].

(* Proven with Restrict ->  Par1 -> Par2 -> Prefix "a" *)
Definition q1d1 := PRestrict (PPar (PPar (PPrefix "b" 
                                                 (PPrefix "c" P0))
                                        (PPrefix "d" P0))
                                  (PPrefix "b" P0))
                            ["b" ; "c"].

Theorem q1d1_holds : peval q1d "a" q1d1.
Proof.
  eapply Restrict. eapply Par1. 
  eapply Par2. eapply Prefix.
Qed.


(* Question 2 *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Fixpoint remove (v:string) (s:list string) : list string :=
  match s with
  | [] => []
  | h::t => if eqb_string h v then remove v t else h::(remove v t)
  end.

Fixpoint remove_all (dontwant : list string) (have : list string) 
                  : list string :=
  match dontwant with
  | [] => have
  | h::t => remove_all t (remove h have)
  end.

Inductive Sort : Proc -> (list string) -> Prop :=
  | S_0 : Sort P0 []
  | S_Prefix_lab (a : Act) (p : Proc) (s : string) 
                 (ps : list string) (HLab : a = (Lab s))
                 (H : Sort p ps)
    : Sort (PPrefix (Lab s) p) ([s] ++ ps)
  | S_Prefix_special (p : Proc) (ps : list string)
                     (H: Sort p ps)
    : Sort (PPrefix Special p) ps
  | S_Choice (p1 p2 : Proc) (ps1 ps2 : list string)
      (H1 : Sort p1 ps1) (H2 : Sort p2 ps2)
    : Sort (PChoice p1 p2) (ps1 ++ ps2)
  | S_Par (p1 p2 : Proc) (ps1 ps2 : list string)
      (H1 : Sort p1 ps1) (H2 : Sort p2 ps2)
    : Sort (PPar p1 p2) (ps1 ++ ps2)
  | S_Restrict (p1 : Proc) (x : list string) (ps1 : list string)
      (H : Sort p1 ps1)
    : Sort (PRestrict p1 x) (remove_all x ps1)
.

Inductive is_subset : list string -> list string -> Prop :=
  | subs_nil (xs : list string) : is_subset [] xs
  | subs_headmatch (xs ys : list string) (n:string) (H : is_subset xs ys)
    : is_subset (n::xs) (n::ys)
  | subs_rightextra (xs ys : list string) (n : string) (H : is_subset xs ys)
    : is_subset xs (n::ys)
.

Hint Constructors Sort.
Hint Constructors is_subset.


Fixpoint contains (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | h::t => if eqb_string h x then true else contains x t
  end.

Fixpoint dedup (xs : list string) : list string :=
    match xs with
      | [] => []
      | h::t => if contains h t then dedup t else h::(dedup t)
    end.

Fixpoint SortF (p : Proc) : list string :=
  match p with
  | P0 => []
  | PPrefix a p => 
          dedup (List.app (match a with
                        | Lab s => [s]
                        | Special => []
                        end) (SortF p))
  | PChoice p1 p2 => dedup (List.app (SortF p1) (SortF p2))
  | PPar p1 p2 => dedup (List.app (SortF p1) (SortF p2))
  | PRestrict p xs =>
          dedup (remove_all xs (SortF p))
  end.

Definition q2 :=
  forall (q q' : Proc) (qs qs' : list string) (a : Act),
        (peval q a q') -> (qs = SortF q)
        -> (qs' = SortF q') -> (is_subset qs qs').

Theorem q2_ans : q2.
Proof. unfold q2.
  intros.
  
Admitted.





























