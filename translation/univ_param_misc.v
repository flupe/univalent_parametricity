From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import Coq.Init.Nat.
Require Import NatBinDefs.
Require Import BinInt BinNat Nnat.
Import Template.Universes.Level.
Require Import String.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

Close Scope hott_list_scope.
Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.

Open Scope type_scope.

Record TermRule := mkTermRule
  { a : global_reference
  ; b : term
  ; ta : term
  ; tb : term
  ; witness : term
  }.


Record TslRes := mkRes
  { trad : term (* the translated term         *)
  ; t₁ : term   (* type of the source term     *)
  ; t₂ : term   (* type of the translated term *)
  ; w  : term   (* witness of relation between the source and translated terms *)
                (* if t : Type, then w : t ⋈ t'
                   otherwise, with t : A,  w : t ≈ t' : A ⋈ A'*)
  }.

Definition tsl_table := Datatypes.list (global_reference * TslRes).

Fixpoint lookup_table (E : tsl_table) (gr : global_reference) : option TslRes :=
	match E with
	| hd :: tl =>
		if gref_eq_dec gr (fst hd) then Some (snd hd)
		else lookup_table tl gr
	| [] => None
	end.

Definition suffix (n : name) s : name :=
  match n with
  | nAnon     => nAnon
  | nNamed id => nNamed (id ++ s)
  end.

Definition with_default {A} (d : A) (x : option A) : A :=
  match x with
  | Some x => x
  | None => d
  end.


Local Existing Instance config.default_checker_flags.
Local Existing Instance default_fuel.

(* VERY WIP *)
Definition UR_id (A : Type) : A ⋈ A.
	apply Canonical_UR, Equiv_id.
Defined.

Print FP_forall_ur_type.
Quote Definition f := @FP_forall_ur_type.
Print f.


Definition mkForallUR (A A' eA B B' eB: term) := tApp (<% FP_forall_ur_type %>) [A; A'; eA; B; B'; eB].

Definition UR_apply (e a b: term) :=
  tApp (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR"
                ; inductive_ind  := 0 |}, 2, 0)%core
              (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"
                       ; inductive_ind  := 0 |}, 2, 1)%core 
                     (e)))
       [a; b].


(* Utilities to provide correct by construction translation rules *)
Arguments existT {_ _} _ _.
Definition type_subst := { A : Type & { B : Type & A ⋈ B }}.
Definition term_subst := { A : Type & { B : Type & { w : UR A B & { a : A & {b : B & a ≈ b }}}}}.

Definition subst_type {A B : Type} (ur : A ⋈ B) : type_subst := existT A (existT B ur).
Definition subst_term {A B : Type} {w : UR A B} (a : A) (b : B) (e : @ur A B w a b) : term_subst :=
  existT A (existT B (existT w (existT a (existT b e)))).

Record TranslationRule := mkTslTable
  { type_rules : Datatypes.list type_subst
  ; term_rules : Datatypes.list term_subst
  }.

Definition test : TranslationRule :=
  mkTslTable [ subst_type compat_nat_N ]
             [ ].


(* Fixpoint extract_type_rules (t : Datatypes.list type_subst) : TemplateMonad tsl_table :=
  match t with
  | [] => ret []
  | (existT A (existT B ur)) :: t =>
      A <- tmQuote A ;;
      B <- tmQuote B ;;
      ur <- tmQuote ur ;;
      rest <- extract_type_rules t ;;
      tmPrint rest ;;
      ret []
  end.

Run TemplateProgram (extract_type_rules (type_rules test)). *)


Fixpoint tsl_rec (fuel : nat) (E : tsl_table) (Σ : global_env_ext) (Γ₁ : context) (Γ₂ : context) (t : term)
  : tsl_result TslRes :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
	match t with
  | tSort s => ret (mkRes t todo todo (tApp <% UR_id %> [t]))

  | tInd ind u =>
      match lookup_table E (IndRef ind) with
      | None => ret (mkRes t todo todo (tApp <% UR_id %> [t]))
      | Some tsl => ret tsl
      end
  
  | tConstruct i n univs =>
      match lookup_table E (ConstructRef i n) with
      | None => ret (mkRes t todo todo todo)
      | Some tsl => ret tsl
      end

  (* TODO: infer types from local context *)
  | tRel x => ret (mkRes (tRel x) todo todo (tRel (x * 3)))

  | tLambda n A B =>
      rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
      rB <- tsl_rec fuel E Σ (vass n A :: Γ₁) (vass n (trad rA) :: Γ₂) B ;;
      ret {| trad := tLambda n (trad rA) (trad rB)
          ;  t₁ := tProd n A        (t₁ rB)
          ;  t₂ := tProd n (trad rA) (t₂ rB)
          ;  w := tLambda (suffix n "₁") A (
                    tLambda (suffix n "₂") (trad rA) (
                      tLambda (suffix n "ᵣ") (UR_apply (w rA) (tRel 1) (tRel 0)) (
                        w rB
                      )
                    )
                  )
          |}
    
  | tProd n A B =>
      rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
      let B' := tLambda n A B in
      rB <- tsl_rec fuel E Σ Γ₁ Γ₂ B' ;;
      ret {| trad := tProd n (trad rA) (tApp (trad rB) [tRel 0])
          ;  t₁ := todo
          ;  t₂ := todo
          ;  w  := mkForallUR A (trad rA) (w rA) B' (trad rB) (w rB)
          |}

	| _ => ret (mkRes t todo todo todo)
  end
  end.

Close Scope type_scope.

Definition convert {A} (E : tsl_table) (x : A) :=
  p <- tmQuoteRec x;;

  match p with
  | (env, term) =>
    result <- tmEval lazy (tsl_rec fuel E (empty_ext []) [] [] term) ;;
    match result with
    | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
    | Success res =>
        tmPrint "obtained translation: " ;;
        tmEval all (trad res) >>= tmUnquote >>= tmPrint
    end
  end.

Open Scope type_scope.


Definition Can_nat_N : nat ≈ N := Canonical_UR nat N.

Definition nat_N_tsl : tsl_table :=
	[ (IndRef (mkInd "Coq.Init.Datatypes.nat" 0), mkRes <% N %> <% Type %> <% Type %> <% compat_nat_N %>)
	; (ConstructRef (mkInd "Coq.Init.Datatypes.nat" 0) 0, mkRes <% 0%N %> <% nat %> <% N %> todo)
  ].

Unset Strict Unquote Universe Mode.

Run TemplateProgram (convert nat_N_tsl (fun (x : nat) => 0)).