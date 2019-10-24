From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Require Import Arith.Compare_dec.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import Coq.Init.Nat.
Require Import NatBinDefs.
Require Import BinInt BinNat Nnat.
Import Template.Universes.Level.
Require Import String.

Close Scope hott_list_scope.
Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.

Open Scope type_scope.

Definition tsl_table := Datatypes.list (global_reference * term).

Fixpoint lookup_table (E : tsl_table) (gr : global_reference) : option (term) :=
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

Definition mkForallUR (A A' eA : term) := tApp (<% FP_forall_ur_type %>) [A; A'; eA].

Definition UR_apply (e a b: term) :=
  tApp (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR"; inductive_ind := 0 |}, 2, 0)%core
    (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"; inductive_ind := 0 |}, 2, 1)%core (e)))
    [a; b]. 

Fixpoint tsl_rec (Σ : global_env_ext) (Γ : context) (E : tsl_table) (t : term)
	: tsl_result term :=
	match t with
  | tSort s => ret (tApp <% UR_id %> [t])
  | tInd ind u => ret (with_default (tApp <% UR_id %> [t]) (lookup_table E (IndRef ind)))

  | tRel x => ret (tRel (x * 3))

  | tLambda n A B =>
      Ar <- tsl_rec Σ Γ E A ;;
      Br <- tsl_rec Σ Γ E B ;;
      ret (tLambda (suffix n "₁") A
            (tLambda (suffix n "₂") A
              (tLambda (suffix n "ᵣ") (UR_apply Ar (tRel 1) (tRel 0)) Br)))
  
  | tProd n A B => todo

	| _ => ret todo
  end.

Close Scope type_scope.

Definition convert {A} (E : tsl_table) (x : A) :=
  p <- tmQuoteRec x;;
  
  match p with
  | (env, term) =>
    result <- tmEval lazy (tsl_rec (empty_ext []) [] E term) ;;
    match result with
    | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
    | Success term' =>
        tmPrint "obtained translation: " ;;
        tmEval lazy term' >>= tmUnquote >>= tmPrint ;;
        typ <- tmQuote (nat -> nat)%type ;;
        typ <- tmEval lazy (tsl_rec (empty_ext []) [] E typ) ;;
        match typ with
        | Success typ =>
            tmEval lazy (tApp typ [term; term]) >>= tmUnquote >>= tmPrint
        | Error e =>
            print_nf e
        end
    end
  end.

Open Scope type_scope.


Definition Can_nat_N : nat ≈ N := Canonical_UR nat N.

Definition nat_N_tsl : tsl_table :=
	[ (IndRef (mkInd "Coq.Init.Datatypes.nat" 0), (<% N %>, <% compat_nat_N %>))
	].

Unset Strict Unquote Universe Mode.

Run TemplateProgram (convert nat_N_tsl (fun (x : nat) => x)).