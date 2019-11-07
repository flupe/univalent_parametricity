From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import Coq.Init.Nat.
Require Import NatBinDefs NatBinALC.
Require Import BinInt BinNat Nnat.
Import Template.Universes.Level.
Require Import String.
Require Import UnivalentParametricity.theories.Transportable.
Require Import UnivalentParametricity.translation.utils.

Close Scope hott_list_scope.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope type_scope.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

Local Existing Instance config.default_checker_flags.
Local Existing Instance default_fuel.

Quote Definition tSigma := @sigT.
Quote Definition tPair := @existT.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].


Run TemplateProgram (
  define_translation "tsl_nat_N"%string
    [ subst_type compat_nat_N ]
    [ subst_term compat_add
    ; subst_term compat_zero
    ; subst_term compat_mul
    ; subst_term compat_div
    ; subst_term compat_pow
    ; subst_term compat_sub
    ; subst_term compat_le
    ]).


(* VERY WIP *)
Definition UR_id (A : Type) : A ≈ A.
	apply Canonical_UR, Equiv_id.
Defined.

Definition ur_id {A : Type} (x : A) : @ur A A (Ur (UR_id A)) x x.
  pose (w := UR_id A).
  pose (ur_coh x x).
  unfold univalent_transport in e.
  simpl ((equiv w) x) in e.
  apply e.
  reflexivity.
Defined.

Definition mkForallUR (A A' eA B B' eB: term) := tApp (H4CK <% FP_forall_ur_type %>) [A; A'; eA; B; B'; eB].

Definition UR_apply (e a b: term) :=
  tApp (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR"
                ; inductive_ind  := 0 |}, 2, 0)%core
              (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"
                       ; inductive_ind  := 0 |}, 2, 1)%core 
                     (e)))
       [a; b].

Definition UR_equiv (e : term) :=
  tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"; inductive_ind  := 0 |}, 2, 0)%core (e).


Fixpoint tsl_rec0 (n : nat) (o : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if Nat.leb n k then (* global variable *) tRel (3 * (k - n) + n + o)
                        else (* local  variable *) t
  | tEvar k ts      => tEvar k (List.map (tsl_rec0 n o) ts)
  | tCast t c a     => tCast (tsl_rec0 n o t) c (tsl_rec0 n o a)
  | tProd na A B  => tProd na (tsl_rec0 n o A) (tsl_rec0 (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (List.map (tsl_rec0 n o) lu)
  | tProj p t => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

Open Scope string_scope.

(* HACKISH UNIVERSE HANDLING *)
Definition univ_transport (l1 l2 : Level.t) := tConst "UnivalentParametricity.theories.HoTT.univalent_transport" [l1; l2].
Definition ur_refl := tConst "UnivalentParametricity.theories.UR.ur_refl" [lSet; lSet; lSet].

Definition mk_transport (A B : term) (sA sB : Level.t) (eq t : term) := tApp (univ_transport sA sB) [A; B; eq; t].

Print prod.

(* Fixpoint correct (n : nat) (t : term) :=
  match t with
  | tRel k =>
      if Nat.leb n k then t else t
  | tEvar k ts => tEvar k (List.map (correct n o) ts)
  | tCast t c a => tCast (correct n o t) c (tsl_rec0 n o a)
  | tProd na A B => tProd na (correct n o A) (correct (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (List.map (tsl_rec0 n o) lu)
  | tProj p t => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end. *)


Fixpoint tsl_rec' (lift : bool) (fuel : nat) (E : tsl_table) (Σ : global_env_ext) (Γ₁ : context) (Γ₂ : context) (t : term)
  : tsl_result TslRes :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  let tsl_rec := tsl_rec' false in
	match t with
  | tSort s => ret (mkRes t (tApp <% UR_id %> [t]))

  | tProd n A B =>
    rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
    let B' := tLambda n A B in
    rB <- tsl_rec fuel E Σ Γ₁ Γ₂ B' ;;
    ret {| trad := tProd n (trad rA) (tApp (trad rB) [tRel 0])
                   (* {A A'} {HA : UR A A'} {P : A -> Type} {Q : A' -> Type} (eB : forall x y (H:x ≈ y), P x ⋈ Q y) *)
        ;  w    := mkForallUR A (trad rA) (w rA) B' (trad rB) (tApp (H4CK <% @forall_from_ur %>) [A; trad rA; w rA; B'; trad rB; w rB])
        |}

  | tInd ind u =>
      match lookup_table E (IndRef ind) with
      | Some tsl => ret tsl
      | None     => ret (mkRes t (tApp <% UR_id %> [t]))
      end

  | tConstruct i n univs =>
      match lookup_table E (ConstructRef i n) with
      | Some tsl => ret tsl
      | None =>
          match lift, infer' Σ Γ₁ t with
          | true, Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp (univ_transport lSet lSet) [ typ; trad typ'; UR_equiv (w typ') ; t ])
                (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
          | true, TypeError e => Error (TypingError e)
          | false, _ => Error TranslationNotHandeled
          end
      end
  
  | tConst n univs =>
      match lookup_table E (ConstRef n) with
      | Some tsl => ret tsl
      | None =>
          match lift, infer' Σ Γ₁ t with
          | true, Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp (univ_transport lSet lSet) [ typ; trad typ'; UR_equiv (w typ') ; t ])
                (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
          | true, TypeError e => Error (TypingError e)
          | false, _ => Error TranslationNotHandeled
          end
      end

  | tRel x => ret (mkRes t (tRel (x * 3)))

  | tLambda n A B =>
      rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
      rB <- tsl_rec fuel E Σ (vass n A :: Γ₁) (vass n (trad rA) :: Γ₂) B ;;
      ret {| trad := tLambda n (trad rA) (trad rB)
          ;  w := tLambda (suffix n "₁") A (
                    tLambda (suffix n "₂") (trad rA) (
                      tLambda (suffix n "ᵣ") (UR_apply (w rA) (tRel 1) (tRel 0)) (
                        w rB
                      )
                    )
                  )
          |}
  
  | tApp f args =>
      match tsl_rec' false fuel E Σ Γ₁ Γ₂ f with
      | Success rf =>
          args' <- monad_map (tsl_rec' true fuel E Σ Γ₁ Γ₂) args ;;
          ret (mkRes (tApp (trad rf) (List.map trad args'))
                    (tApp (w rf) (List.flat_map (fun (p : term * TslRes) => 
                              [tsl_rec0 0 2 (fst p); tsl_rec0 0 1 (trad (snd p)); w (snd p)]) (zip args args'))))
      | Error _ =>
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              let t' := mk_transport typ (trad typ') lSet lSet (UR_equiv (w typ')) t in
              ret (mkRes t' (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
 
          | TypeError t => Error TranslationNotHandeled
          end
      end

	| _ => ret (mkRes t todo)
  end
  end.

Close Scope type_scope.


Inductive ResultType := Term | Witness.


Definition convert {A} (ΣE : (global_env * tsl_table)%type) (t : ResultType) (x : A) :=
  p <- tmQuoteRec x ;;

  let term := p.2 in
  let env := empty_ext (app (fst ΣE) p.1) in
  let E := snd ΣE in

  result <- tmEval lazy (tsl_rec' true fuel E env [] [] term) ;;
  
  match result with
  | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
      
  | Success rt =>
      tmPrint "obtained translation: " ;;
      t <- tmEval all (match t with Term => trad rt | Witness => (w rt) end);;
      tmUnquote t >>= tmPrint
  end.
(* 
  Definition translate {A} (ΣE : (global_env * tsl_table)%type) (name : ident) (x : A) :=
  p <- tmQuoteRec x ;;

  let term := p.2 in
  let env := empty_ext (app (fst ΣE) p.1) in
  let E    := snd ΣE in

  match infer' env [] term with
  | Checked typ =>
    result  <- tmEval lazy (tsl_rec' true fuel E env [] [] term) ;;
    result' <- tmEval lazy (tsl_rec' true fuel E env [] [] typ) ;;
    match result, result' with
    | Error e, _ | _, Error e =>
        print_nf e ;;
        fail_nf "Translation failed"
    
    | Success res, Success res' =>
        tmUnquote (trad res) >>= tmDefinition name ;;
        tmUnquote (w res) >>= tmDefinition (name ++ "_ur")
    end
  | TypeError t => fail_nf (string_of_type_error t)
  end. *)


(* EXAMPLE *)

Parameter f : nat -> nat.

Run TemplateProgram (convert tsl_nat_N Witness (0)).
Run TemplateProgram (convert tsl_nat_N Witness (f 5)).

Set Printing Universes.

Run TemplateProgram (convert tsl_nat_N Witness (5 + 0)).

Run TemplateProgram (convert tsl_nat_N Witness (f)).
Run TemplateProgram (convert tsl_nat_N Term    (fun (x:nat) => x * x)).
Run TemplateProgram (convert tsl_nat_N Witness (fun (x:nat) => x * x)).

Run TemplateProgram (convert tsl_nat_N Term (fun (x:nat) => pow x 2 + 2 * x + 1)).
Run TemplateProgram (convert tsl_nat_N Witness (fun (x:nat) => pow x 2 + 2 * x + 1)).

Run TemplateProgram (convert tsl_nat_N Witness (fun (x:nat) => x + 3)).

(* then it fails *)
Run TemplateProgram (convert tsl_nat_N Term (fun (x : nat) => S x)).
