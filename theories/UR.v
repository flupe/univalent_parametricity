(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import HoTT CanonicalEq.
Require Import UnivalentParametricity.theories.Transportable.
Require Import URTactics.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

(* basic classes for univalent relations *)

Class UR A B := {
  ur : A -> B -> Type 
}.

Arguments ur {_ _ _} _ _.

Notation "x ≈ y" := (ur x y) (at level 20).

Class UR_Coh@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_coh : forall (a a':A), Equiv (a = a') (a ≈ (↑ a')) }.

Class UR_Type A B :=
  { equiv :> A ≃ B;
    Ur :> UR A B;
    Ur_Coh:> UR_Coh A B equiv Ur;
    Ur_Can_A :> Canonical_eq A;
    Ur_Can_B :> Canonical_eq B;
  }.

Infix "⋈" := UR_Type (at level 25).

Arguments equiv {_ _} _.
Arguments Ur {_ _} _.
Arguments Ur_Coh {_ _} _.
Arguments Ur_Can_A {_ _} _.
Arguments Ur_Can_B {_ _} _.

(* some facilities to create an instance of UR_Type *)

Definition UR_gen A : UR A A := {| ur := (eq A) |}.

Definition UR_inverse A B `{UR A B} : UR B A := {| ur := fun b a => ur a b |}.

Class URRefl@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_refl_ : forall a : A,  a ≈ ↑ a 
}.

Arguments ur_refl_ {_ _ _ _ _} _.

(* This is the Black Box Property *)

Definition ur_refl {A B: Type} {e : A ⋈ B} : forall a : A,  a ≈ ↑ a := fun a => (ur_coh a a) eq_refl. 

Hint Extern 100 (_ ≈ _) => unshelve notypeclasses refine  (ur_refl _): typeclass_instances.


Definition URIsEq@{i j k} A B (e : A ≃ B) (H: UR@{i j k} A B) (H:URRefl@{i j k} A B e H)
  :=  forall (a a':A), @IsEquiv (a = a') (a ≈ (↑ a'))
                                (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a)).

Existing Class URIsEq.
Typeclasses Transparent URIsEq.

Instance Ur_Coh_from_ur_refl A B (e:A ≃ B) (H:UR A B)
           (Hrefl : URRefl A B e H) : URIsEq A B e H Hrefl ->
                                       UR_Coh A B e H.
Proof.
  intros Hiseq. econstructor. intros a a'.
  exact (BuildEquiv _ _ (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a))
                     (Hiseq a a')).
Defined.

(* The definition of Ur_coh given in the ICFP'18 paper is equivalent to *)
(* the definition given here, but technically, this one is more convenient to use *)

Definition alt_ur_coh {A B:Type} (e:A ≃ B) (H:UR A B) (HCoh : UR_Coh A B e H) (einv := Equiv_inverse e):
  forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b).
Proof.
  intros a b. cbn. 
  refine (transport_eq (fun X => (a ≈ X) ≃ (a = univalent_transport b))
                       (e_sect _ b) _). apply Equiv_inverse. 
    unshelve refine (ur_coh _ _). 
Defined.

Definition alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:UR A B) (einv := Equiv_inverse e)
           (HCoh : forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)):
  UR_Coh A B e H.
Proof.
  refine (Build_UR_Coh _ _ _ _ _). intros a a'.
  apply Equiv_inverse. 
  refine (transport_eq (fun X => (a ≈ univalent_transport a') ≃ (a = X))
                       (e_sect _ a') _). 
    unshelve refine (HCoh _ _). 
Defined.


(* Definition of univalent relation for basic type constructors *)

(*! Universe !*)

Instance UR_Type_def@{i j} : UR@{j j j} Type@{i} Type@{i} :=
  Build_UR@{j j j} _ _ UR_Type@{i i i}.

(*! Forall !*)

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.


Class URForall_Type_class A A' {HA : UR A A'}  (P : A -> Type) (Q : A' -> Type) :=
  { transport_ :> Transportable P;
    ur_type :> forall x y (H:x ≈ y), P x ⋈ Q y}.

Arguments ur_type {_ _ _ _ _} _. 

Definition URForall_Type A A' {HA : UR A A'} :
  UR (A -> Type) (A' -> Type)
  :=
    {| ur := fun P Q => URForall_Type_class A A' P Q |}.

Definition URForall A A' (B : A -> Type) (B' : A' -> Type) {HA : UR A A'} 
           {HB: forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (forall x, B x) (forall y, B' y)
  :=
  {| ur := fun f g => forall x y (H:x ≈ y), f x ≈ g y |}.

Hint Extern 0 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall_Type A A' _); cbn in *; intros : typeclass_instances.

Hint Extern 1 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition ur_hprop A A' (H : A ⋈ A') (HA: forall x y:A, x = y) (x:A) (y:A')
  : x ≈ y. 
  intros. apply (alt_ur_coh _ _ _ _ ). apply HA. 
Defined.   


Definition UR_Type_equiv (A A' : Type) (eA : A ⋈ A') (eA': A ≃ A')
  (e  : equiv eA = eA') : 
  eA =
  Build_UR_Type _ _ eA' (Ur eA)
                (transport_eq (fun X => UR_Coh A A' X _) e (Ur_Coh eA)) _ _. 
  destruct e. reflexivity.
Defined. 

Definition UR_Type_eq (A A' : Type) (eA eA': A ⋈ A')
           (equiv_eq  : equiv eA = equiv eA')
           (ur_eq  : Ur eA = Ur eA')
           (coh_eq  : transport_eq (fun X => UR_Coh A A' _ X) ur_eq (transport_eq (fun X => UR_Coh A A' X _) equiv_eq (Ur_Coh eA))
                      = Ur_Coh eA')
           (canonA_eq  : eA.(Ur_Can_A) = eA'.(Ur_Can_A))
           (canonB_eq  : eA.(Ur_Can_B) = eA'.(Ur_Can_B))
  : eA = eA'. 
  destruct eA, eA'.
  cbn in *. rewrite <- coh_eq. destruct equiv_eq, ur_eq, canonA_eq, canonB_eq.
  reflexivity.
Defined.                  

Definition  transport_Ur_Coh (A A': Type)
            (equiv : A ≃ A')
            (_ur _ur' : A -> A' -> Type)
            (ur_coh : forall a a' : A, (a = a') ≃ (_ur a (equiv a')))
            (e : _ur = _ur')
  :   transport_eq (fun X => UR_Coh A A' equiv {| ur := X |}) e
                   (Build_UR_Coh _ _ equiv {| ur := _ur |} ur_coh)
      =
      Build_UR_Coh _ _ equiv {| ur := _ur' |} (fun a a' => transport_eq (fun X =>
                                               (a = a') ≃ (X a (equiv a'))) e (ur_coh a a')).
  destruct e. reflexivity.
Defined.

Definition UR_Equiv_refl (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{UR A B} : UR B B :=
  {| ur := fun b b' => ↑ b ≈  b' |}.
