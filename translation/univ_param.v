From MetaCoq Require Import Template.All Checker.All.
From MetaCoq.Translations Require Import translation_utils.
Require Import Arith.Compare_dec.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import NatBinDefs.
Require Import Coq.Init.Nat.
Require Import BinInt BinNat Nnat.

Close Scope hott_list_scope.
Close Scope type_scope.
Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.


Definition fmap {P} {w : Monad P} {A B} (f : A -> B) (m : P A) : P B :=
    m >>= fun x => ret (f x).

Definition liftA2 {P} {w : Monad P} {A B C} (f : A -> B -> C) (ma : P A) (mb : P B) : P C :=
    a <- ma ;;
    b <- mb ;;
    ret (f a b).

Infix "$>"  := fmap (at level 10, left associativity).
Infix "<*>" := (liftA2 id) (at level 10, left associativity).


Definition with_default {A} (d : A) (x : option A) : A :=
    match x with
    | Some x => x
    | None => d
    end.


Local Existing Instance config.default_checker_flags.
Local Existing Instance default_fuel.

Fixpoint tsl_rec (fuel : nat) (Σ : global_env_ext) (Γ : context) (E : tsl_table) (t : term)
    : tsl_result term :=
    match fuel with
    | O => raise NotEnoughFuel
    | S fuel =>
    match t with
    | tConst name univ =>
        (* TODO: find body *)
        ret (with_default t (lookup_tsl_table E (ConstRef name)))
    
    | tConstruct i name univ =>
        ret (with_default t (lookup_tsl_table E (ConstructRef i name)))
        
    | tLambda name typ val =>
        tLambda name $> (tsl_rec fuel Σ Γ E typ) <*> (tsl_rec fuel Σ Γ E val)
    
    | tApp fn args =>
        tApp $> (tsl_rec fuel Σ Γ E fn) <*> (monad_map (tsl_rec fuel Σ Γ E) args)
        (* match infer' Σ Γ term with
        | Checked _ => ret term
        | TypeError t => Error (TypingError t) (* TODO: lift to the correct type *)
        end *)

    | tInd ind u =>
        ret (with_default t (lookup_tsl_table E (IndRef ind)))

    | tProd name ty body =>
        tProd name $> (tsl_rec fuel Σ Γ E ty) <*> (tsl_rec fuel Σ Γ E body)
    
    | tRel _
    | tVar _
    | tEvar _ _
    | tSort _
    | tCast _ _ _
    | tLetIn _ _ _ _
    | tCase _ _ _ _
    | tProj _ _
    | tFix _ _
    | tCoFix _ _ => ret t
    end
    end.

Definition poly (n : nat) : nat := pow n 42 + 5 * n.

Notation inat := "Coq.Init.Datatypes.nat".
Notation ibin := "Coq.Numbers.BinNums.N".

Definition ind_nat := mkInd inat 0.
Definition ind_bin := mkInd ibin 0.

Definition nat_rule : tsl_table :=
    [ (ConstRef "Coq.Init.Nat.add", tConst "Coq.NArith.BinNatDef.N.add" [])
    ; (ConstRef "Coq.Init.Nat.sub", tConst "Coq.NArith.BinNatDef.N.sub" [])
    ; (ConstRef "Coq.Init.Nat.mul", tConst "Coq.NArith.BinNatDef.N.mul" [])
    ; (IndRef ind_nat, tInd ind_bin [])
    ; (ConstructRef ind_nat 0, tConstruct ind_bin 0 [])
    ].

(* if I use default fuel, stack overflow *)

Run TemplateProgram (
    term <- tmQuote (fun (n : nat) => 0 * 0) ;;
    tmPrint term ;;
    let term' := (tsl_rec fuel (empty_ext []) [] nat_rule term) in
    term' <- tmEval lazy term' ;; 
    match term' with
    | Error e =>
        print_nf e;;
        fail_nf "Translation error during the translation"
    | Success term' =>
        tmPrint term' ;;
        tmUnquote term' >>= tmPrint
    end).