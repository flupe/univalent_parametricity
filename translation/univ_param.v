From MetaCoq Require Import Template.All.
From MetaCoq.Translations Require Import translation_utils.
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

Definition conversion_rule := (Datatypes.prod (term -> term)  tsl_table)%type. 

Fixpoint tsl_rec (E : conversion_rule) (t : term) : term :=
    match t with
    | tConst name univ as t =>
        match lookup_tsl_table (Datatypes.snd E) (ConstRef name) with
        | Some t' => t'
        | None => t
        end
    
    | tConstruct i name univ as t =>
        match lookup_tsl_table (Datatypes.snd E) (ConstructRef i name) with
        | Some t' => t'
        (* TODO: lift the whole constructor *)
        | None => t
        end
        
    | tLambda name typ val => tLambda name (tsl_rec E typ) (tsl_rec E val)
    
    | tApp t args =>
        tApp (tsl_rec E t) (List.map (tsl_rec E) args)

    | tInd ind u as t =>
        (* We must assume that the type translation is defined *)
        (* Perhaps if it is not we should rename variables and list as black box? *)
        match lookup_tsl_table (Datatypes.snd E) (IndRef ind) with
        | Some t' => t'
        | None => t
        end

    | tProd name ty body as t => tProd name (tsl_rec E ty) (tsl_rec E body)
    
    | tRel _ as t
    | tVar _ as t
    | tEvar _ _ as t
    | tSort _ as t
    | tCast _ _ _ as t
    | tLetIn _ _ _ _ as t
    | tCase _ _ _ _ as t
    | tProj _ _ as t
    | tFix _ _ as t
    | tCoFix _ _ as t => t
    end.

Definition poly (n : nat) : nat := pow n 42 + 5 * n.

Definition ind_nat := mkInd "Coq.Init.Datatypes.nat" 0.
Definition ind_bin := mkInd "Coq.Numbers.BinNums.N" 0.

Definition nat_rule : conversion_rule :=
    (* this is BAD. also, does not work *)
    ( (fun (a : term) =>
        tApp (tConst "UnivalentParametricity.theories.HoTT.univalent_transport" [])
            [tInd ind_nat []; tInd ind_bin []; a])

    , [ (ConstRef "Coq.Init.Nat.add", tConst "Coq.NArith.BinNatDef.N.add" [])
      ; (IndRef ind_nat, tInd ind_bin [])
      ; (ConstructRef ind_nat 0, tConstruct ind_bin 0 [])
      ]).

Run TemplateProgram (
    term <- tmQuote (fun (n : nat) (f: nat -> nat) => f n + f 0) ;;
    tmPrint term ;;
    let term' := (tsl_rec nat_rule term) in
    tmEval cbv term' >>= tmPrint;;
    tmUnquote term' >>= tmPrint
).