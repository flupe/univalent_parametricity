Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP UnivalentParametricity.theories.StdLib.FP Record UnivalentParametricity.theories.Transportable UnivalentParametricity.theories.StdLib.Transportable DecidableEq.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

(* Moving stuff that was in MoreInductive.v related to nat/binnat *)

(* nat ⋈ N *)

Require Import BinInt BinNat Nnat.

Lemma iter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 Pos.iter_op op (Pos.succ p) a = op a (Pos.iter_op op p a).
Proof.
 induction p; simpl; intros; try reflexivity.
 rewrite X. apply IHp.
Defined.

Fixpoint plus_assoc (n m p : nat) : n + (m + p) = n + m + p.
 induction n. cbn. reflexivity.
 cbn. apply ap. apply plus_assoc.
Defined. 
 
Lemma inj_succ p : Pos.to_nat (Pos.succ p) = S (Pos.to_nat p).
Proof.
 unfold Pos.to_nat. rewrite iter_op_succ. reflexivity. 
 apply plus_assoc.
Defined.

Definition is_succ : forall p, {n:nat & Pos.to_nat p = S n}.
Proof.
 induction p using Pos.peano_rect.
 now exists 0.
 destruct IHp as (n,Hn). exists (S n). now rewrite inj_succ, Hn.
Defined. 

Theorem Pos_id (n:nat) : n<>0 -> Pos.to_nat (Pos.of_nat n) = n.
Proof.
 induction n as [|n H]; trivial. now destruct 1.
 intros _. simpl Pos.of_nat. destruct n. reflexivity.
 rewrite inj_succ. f_equal. apply ap. now apply H.
Defined.

Lemma of_nat_succ (n:nat) : Pos.of_succ_nat n = Pos.of_nat (S n).
Proof.
 induction n. reflexivity. simpl. apply ap. now rewrite IHn.
Defined. 

Theorem id_succ (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof.
rewrite of_nat_succ. now apply Pos_id.
Defined.

Lemma inj (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m -> n = m.
Proof.
 intro H. apply (ap Pos.to_nat) in H. rewrite !id_succ in H.
 inversion H. reflexivity. 
Defined.

Theorem Pos2Nat_id p : Pos.of_nat (Pos.to_nat p) = p.
Proof.
 induction p using Pos.peano_rect. reflexivity. 
 rewrite inj_succ. rewrite <- (ap Pos.succ IHp).
 now destruct (is_succ p) as (n,->).
Defined.

Lemma Pos2Nat_inj p q : Pos.to_nat p = Pos.to_nat q -> p = q.
Proof.
 intros H. now rewrite <- (Pos2Nat_id p), <- (Pos2Nat_id q), H.
Defined.

Lemma N2Nat_id a : N.of_nat (N.to_nat a) = a.
Proof.
  destruct a as [| p]; simpl. reflexivity.
  destruct (is_succ p) as [n H]. rewrite H. simpl. apply ap. 
  apply Pos2Nat_inj. rewrite H. apply id_succ.
Defined.

Theorem Pos_id_succ p : Pos.of_succ_nat (Pos.to_nat p) = Pos.succ p.
Proof.
rewrite of_nat_succ, <- inj_succ. apply Pos2Nat_id.
Defined.

Theorem id_succ' (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof.
rewrite of_nat_succ. apply Pos_id. intro H. inversion H.
Defined.

Lemma Nat2N_id n : N.to_nat (N.of_nat n) = n.
Proof.
 induction n; simpl; try reflexivity. apply id_succ'.
Defined. 

Instance IsEquiv_N_nat : IsEquiv N.of_nat.
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - exact N.to_nat. 
  - cbn; intro. exact (Nat2N_id _).
  - cbn; intro. exact (N2Nat_id _).
Defined.


Instance Equiv_N_nat : nat ≃ N.
  refine (BuildEquiv _ _ N.of_nat _).  
Defined.

Instance Equiv_nat_N : N ≃ nat := Equiv_inverse _.

Instance UR_N : UR N N := UR_gen N. 

Instance Decidable_eq_N : DecidableEq N := DecidableEq_equiv nat N _.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_nat_N x y _)
                               : typeclass_instances.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_N_nat x y _)
                               : typeclass_instances.

Instance UR_N_nat : UR N nat | 0.
eapply UR_Equiv; tc.
Defined.

Instance compat_N_nat : N ⋈ nat.
Proof.
  unshelve eexists; try tc.
  econstructor. intros. cbn. rewrite (N2Nat_id _). apply Equiv_id.
Defined. 

Instance UR_nat_N : UR nat N | 0.
eapply UR_Equiv; tc. 
Defined.

Instance compat_nat_N : nat ⋈ N.
Proof.
  unshelve eexists; try tc.
  econstructor. intros. cbn.
  rewrite (Nat2N_id _). apply Equiv_id.
Defined. 

Definition refl_nat_N (n:nat) : n ≈ (↑ n : N) := ur_refl (e:=compat_nat_N) n.
Hint Extern 0 (?n = _) => unshelve refine (refl_nat_N _) : typeclass_instances.


(*****************************)

(* As mentioned in Sections 1 and 6, we can lift functions on 
   binary nats to operate on normal nats, sometimes considerably
   improving performance. *)

Definition nat_pow_ : nat -> nat -> nat := ↑ N.pow.

Print Assumptions nat_pow_.

(* (the use of [Eval compute] in the definition above is to 
   force reduction of some noise produced by the lifting.) *)

Definition nat_pow : nat -> nat -> nat := Eval compute in ↑ N.pow.

Print Assumptions nat_pow.


Definition const0 {A} : A -> nat := fun _ => 0. 

(* with the standard nat function: *)
(* Time Eval vm_compute in let x := Nat.pow 3 15 in const0 x. *)

(* with the lifted function *)
(* Time Eval vm_compute in let x := nat_pow 3 15 in const0 x. *)

 