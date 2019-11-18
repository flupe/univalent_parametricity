From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import UnivalentParametricity.theories.Transportable UnivalentParametricity.translation.utils.
Require Import UnivalentParametricity.translation.univ_param_misc.
Import String MonadNotation List Lists.List.ListNotations.
Require Import String NatBinDefs NatBinALC BinNums BinNat.

Close Scope hott_list_scope.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope type_scope.

Set Universe Polymorphism.

(* Set Type In Type. *)
Local Existing Instance config.type_in_type.
Local Existing Instance default_fuel.

Definition tsl_mind_body (E : tsl_table) (Σ : global_env_ext) (mp : string) (kn : kername)
           (mind : mutual_inductive_body) : tsl_result (tsl_table * list mutual_inductive_body).
  (* handling errors is f u n *)
  refine (pair $> (ret _) <*>
    (sequence (ret (Build_mutual_inductive_body
       $>  (ret mind.(ind_finite))
       <*> (ret mind.(ind_npars))
       <*> (ret mind.(ind_params)) (* this shouldn't be true but works anyway *)
       <*> _
       <*> (ret mind.(ind_universes)))))).

  - refine (let kn' := tsl_kn tsl_ident kn mp in
            fold_left_i (fun E i ind => _ :: _ ++ E)%list mind.(ind_bodies) []).
    + (* ind *)
      exact (IndRef (mkInd kn i), mkRes (tInd (mkInd kn' i) []) todo).
    + (* ctors *)
      refine (fold_left_i (fun E k _ => _ :: E) ind.(ind_ctors) []).
      exact (ConstructRef (mkInd kn i) k, mkRes (tConstruct (mkInd kn' i) k []) todo).

  - eapply sequence.
    refine (mapi _ mind.(ind_bodies)).
    intros i ind.

    refine (Build_one_inductive_body
       $>  (ret (tsl_ident ind.(ind_name)))
       <*> _
       <*> (ret ind.(ind_kelim))
       <*> _
       <*> (ret [])).

    + (* arity  *)
      apply (res <- tsl_rec fuel E Σ [] [] ind.(ind_type) ;;
             ret (trad res)).

    + (* constructors *)
      eapply sequence.
      refine (mapi _ ind.(ind_ctors)).
      intros k ((name, typ), nargs).
      refine (Datatypes.pair $> (Datatypes.pair $> (ret (tsl_ident name)) <*> _) <*> (ret nargs)).

      apply (res <- tsl_rec fuel E Σ [] [] typ ;;
             ret (trad res)).
Defined.


Class Translation :=
  { tsl_id : ident -> ident ;
    tsl_tm : tsl_table -> global_env_ext -> term -> tsl_result TslRes ;

    (* string = ModPath in which the inductive will be declared *)
    tsl_ind : tsl_table -> global_env_ext -> string -> kername -> mutual_inductive_body
              -> tsl_result (tsl_table * list mutual_inductive_body) }.

Instance univ_param : Translation :=
  {| tsl_id := tsl_ident ;
     tsl_tm := fun tsl Σ t => (tsl_rec fuel tsl Σ [] [] t );
     (* Implement and Implement Existing cannot be used with this translation *)
     tsl_ind := fun tsl Σ mp kn mind => (tsl_mind_body tsl Σ mp kn mind) |}.

Open Scope string_scope.

Definition Translate {tsl : Translation} (E : tsl_table) (Σ : global_env_ext) (id : ident)
  : TemplateMonad (tsl_table * global_env_ext) :=
  tmDebug ("Translate" ++ id);;
  gr <- tmAbout id ;;
  tmDebug gr ;;

  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (IndRef (mkInd kn n)) =>
      mp <- tmCurrentModPath tt ;;
      d  <- tmQuoteInductive id ;;
      tmPrint d ;;
      d' <- tmEval lazy (tsl_ind E Σ mp kn d) ;;

      match d' with
      | Error e =>
          print_nf e ;;
          fail_nf ("Error during the translation of the inductive " ++ id)

      | Success (E', decls) =>
          tmPrint decls ;;
          monad_iter tmMkInductive' decls ;;
          let Σ' := add_global_decl (InductiveDecl kn d) Σ in
          let E' := (E' ++ E)%list in
          Σ' <- tmEval lazy Σ' ;;
          E' <- tmEval lazy E' ;;
          tmMsg (kn ++ " has been translated.") ;;
          ret (E', Σ')
      end

  | _ => fail_nf "Translation not supported"
  end.



(* EXAMPLE *)

Inductive Z :=
  | neg : nat -> Z
  | pos : nat -> Z.

Run TemplateProgram (Translate (snd tsl_nat_N) (empty_ext []) "Z").

Definition t : Zᵗ := negᵗ 4%N.
