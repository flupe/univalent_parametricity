From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import UnivalentParametricity.theories.Transportable UnivalentParametricity.translation.utils.
Import String MonadNotation List Lists.List.ListNotations.
Require Import String NatBinDefs NatBinALC.
Import Template.Universes.Level.
From TypingFlags Require Import Loader.

Set Type In Type.

Close Scope hott_list_scope.
Open Scope list_scope.
Open Scope nat_scope.
Open Scope type_scope.

Set Universe Polymorphism.

Local Existing Instance config.type_in_type.
Local Existing Instance default_fuel.


Quote Definition tSigma := @sigT.
Quote Definition tPair := @existT.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].


(* nat to NatBin translation table *)
Run TemplateProgram (
  define_translation "tsl_nat_N"%string
    [ subst_type compat_nat_N ]
    [ subst_term compat_add
    ; subst_term compat_succ
    ; subst_term compat_zero
    ; subst_term compat_mul
    ; subst_term compat_div
    ; subst_term compat_pow
    ; subst_term compat_sub
    ; subst_term compat_le
    ]).


(* Utilities for the translation *)
Definition UR_id (A : Type) : A ⋈ A.
	apply Canonical_UR, Equiv_id.
Defined.


(* Given e : A ⋈ B, a : A, b : B, returns a ≈ b with the given UR *)
Definition ur_of (e a b: term) :=
  tApp (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR"
                ; inductive_ind  := 0 |}, 2, 0)%core
          (tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"
                  ; inductive_ind  := 0 |}, 2, 1)%core 
            (e))) [a; b].

(* Given a term e :  A ⋈ B, returns the projection onto UR_Equiv e : A ≃ B *)
Definition proj_equiv (e : term) :=
  tProj ({| inductive_mind := "UnivalentParametricity.theories.UR.UR_Type"
          ; inductive_ind  := 0 |}, 2, 0)%core e.

(* ↑ (TODO: handle universes) *)
Definition univ_transport := <% @univalent_transport %>.
Definition ur_refl        := <% @ur_refl %>.

(* Given A, B, eq : A ≃ B, t : A, returns ↑ t : B *)
Definition mk_transport (A B eq t : term) := tApp univ_transport [A; B; eq; t].

(* Fixpoint replace_with' {A} (a' a b : Datatypes.list A) :=
  match  a, b with
  | _, [] => []
  | xa :: ta, _ :: tb => xa :: (replace_with' a' ta tb)
  | [], _ :: tb =>
      match a' with
      | [] => b
      | xa :: ta => xa :: (replace_with' a' ta tb)
      end
  end.

Definition replace_with {A} a b := @replace_with' A a a b. *)


Definition mkForallUR (A A' eA B B' eB: term) := tApp <% FP_forall_ur_type %> [A; A'; eA; B; B'; eB].


Fixpoint tsl_rec0 (n : nat) (o : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if Nat.leb n k then (* global variable *) tRel (3 * (k - n) + n + o)
                        else (* local  variable *) t
  | tEvar k ts      => tEvar k (List.map (tsl_rec0 n o) ts)
  | tCast t c a     => tCast (tsl_rec0 n o t) c (tsl_rec0 n o a)
  | tProd na A B    => tProd na (tsl_rec0 n o A) (tsl_rec0 (n+1) o B)
  | tLambda na A t  => tLambda na (tsl_rec0 n o A) (tsl_rec0 (n+1) o t)
  | tLetIn na t A u => tLetIn na (tsl_rec0 n o t) (tsl_rec0 n o A) (tsl_rec0 (n+1) o u)
  | tApp t lu       => tApp (tsl_rec0 n o t) (List.map (tsl_rec0 n o) lu)
  | tProj p t       => tProj p (tsl_rec0 n o t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.

(* 
Definition test {A B} `{A ⋈ B} (w : forall (x:A) (y:B), x ≈ y -> A ⋈ B) : (forall (x : A) (y : B), x ≈ y -> (fun _ : A => A) x ⋈ (fun _ : B => B) y).
  apply w.
Defined. *)

Fixpoint tsl_rec (fuel : nat) (E : tsl_table) (Σ : global_env_ext) (Γ₁ : context) (Γ₂ : context) (t : term)
  : tsl_result TslRes :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
	match t with
  | tSort s => ret (mkRes t (tApp <% UR_id %> [t]))

  | tProd n A B =>
    rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
    let B' := tLambda n A B in
    rB <- tsl_rec fuel E Σ Γ₁ Γ₂ B' ;;

    (* this is undesirable, but for now we cannot do better *)

    ret {| trad := tProd n (trad rA) (tApp (trad rB) [tRel 0])
          ;  univs := []
                (* {A A'} {HA : UR A A'} {P : A -> Type} {Q : A' -> Type} (eB : forall x y (H:x ≈ y), P x ⋈ Q y) *)
          ;  w := mkForallUR A (trad rA) (w rA) B' (trad rB) (tApp (<% @forall_from_ur %>) [A; trad rA; w rA; B'; trad rB; w rB])
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
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp univ_transport [ typ; trad typ'; proj_equiv (w typ') ; t ])
                (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
          | TypeError e => Error (TypingError e)
          end
      end
  
  | tConst n univs =>
      match lookup_table E (ConstRef n) with
      | Some tsl => ret tsl
      | None =>
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp univ_transport [ typ; trad typ'; proj_equiv (w typ') ; t ])
                (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
          | TypeError e => Error (TypingError e)
          end
      end

  | tRel x => ret (mkRes t (tRel (x * 3)))

  | tLambda n A B =>
      rA <- tsl_rec fuel E Σ Γ₁ Γ₂ A ;;
      rB <- tsl_rec fuel E Σ (vass n A :: Γ₁) (vass n (trad rA) :: Γ₂) B ;;
      ret {| trad := tLambda n (trad rA) (trad rB)
          ; univs := []
          ;  w := tLambda (suffix n "₁") A (
                    tLambda (suffix n "₂") (trad rA) (
                      tLambda (suffix n "ᵣ") (ur_of (w rA) (tRel 1) (tRel 0)) (
                        w rB
                      )
                    )
                  )
          |}
  
  | tApp f args =>
      rf    <- tsl_rec fuel E Σ Γ₁ Γ₂ f ;;
      args' <- monad_map (tsl_rec fuel E Σ Γ₁ Γ₂) args ;;
      
      ret (mkRes (tApp (trad rf) (List.map trad args'))
                 (tApp (w rf) (List.flat_map (fun (p : term * TslRes) =>
                              [tsl_rec0 0 2 (fst p); tsl_rec0 0 1 (trad (snd p)); w (snd p)]) (zip args args'))))

	| _ => ret (mkRes t todo)
  end
  end.

Close Scope type_scope.


Inductive ResultType := Term | Witness.


Open Scope string_scope.
Definition convert {A} (ΣE : (global_env * tsl_table)%type) (t : ResultType) (x : A) :=
  p <- tmQuoteRec x ;;

  tmPrint p ;;

  let term := p.2 in
  let env := empty_ext (app (fst ΣE) p.1) in
  let E := snd ΣE in

  result <- tmEval lazy (tsl_rec fuel E env [] [] term) ;;
  
  match result with
  | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
      
  | Success rt =>
      tmPrint "obtained translation: " ;;
      t <- tmEval all (match t with Term => trad rt | Witness => (w rt) end);;
      tmUnquote t >>= tmPrint
  end.

Definition translate {A} (ΣE : (global_env * tsl_table)%type) (name : ident) (x : A) :=
  p <- tmQuoteRec x ;;
  p' <- tmQuoteRec A ;;

  let term := p.2 in
  let typ  := p'.2 in 
  let env  := empty_ext (app (fst ΣE) p.1) in
  let E    := snd ΣE in

  result  <- tmEval lazy (tsl_rec fuel E env [] [] term) ;;

  match result with
  | Error e =>
      print_nf e ;;
      fail_nf "Translation failed"
    
  | Success res =>
      (* let t := (pair (trad res') (tLambda nAnon (trad res') (UR_apply (w res') (term) (trad res))) (trad res) (w res)) in
      tmUnquote t >>= tmDefinition name *)
      tmPrint (w res) ;;
      tmMkDefinition name (trad res) ;;
      tmMkDefinition (name ++ "_ur") (w res)
  end.

(* EXAMPLE *)

Unset Strict Unquote Universe Mode.

Parameter f : nat -> nat.
Parameter x : nat.

Run TemplateProgram (translate tsl_nat_N "poly" (fun (x : nat) => x)).
Check (poly_ur : (fun (x : nat) => x) ≈ poly).

Run TemplateProgram (translate tsl_nat_N "test" (f 5)).