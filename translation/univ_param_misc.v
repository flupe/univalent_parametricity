From MetaCoq Require Import Template.All Checker.All Template.Universes.
From MetaCoq.Translations Require Import translation_utils.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import Coq.Init.Nat.
Require Import NatBinDefs NatBinALC.
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

Fixpoint zip {A B : Type} (ta : Datatypes.list A) (tb : Datatypes.list B) : Datatypes.list (A * B) :=
  match ta, tb with
  | a :: ta, b :: tb => (a, b) :: zip ta tb
  | _, _ => []
  end.

Record TslRes := mkRes
  { trad : term (* the translated term *)
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

(* HACK AHEAD *)
Fixpoint H4CK (a : term) :=
  match a with
  | tConst n u => tConst n (List.map (fun x => lSet) u)
  | tApp f args => tApp (H4CK f) (List.map H4CK args)
  | tLambda n A B => tLambda n (H4CK A) (H4CK B)
  | _ => a
  end.

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

(* HACKISH UNIVERSE HANDLING *)
Definition univ_transport := tConst "UnivalentParametricity.theories.HoTT.univalent_transport" [lSet; lSet].
Definition ur_refl := tConst "UnivalentParametricity.theories.UR.ur_refl" [lSet; lSet; lSet].

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
      | None => Error TranslationNotHandeled  (* TODO *)
      end
  
  | tConst n univs =>
      match lookup_table E (ConstRef n) with
      | Some tsl => ret tsl
      | None => Error TranslationNotHandeled  (* TODO *)
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
      match tsl_rec fuel E Σ Γ₁ Γ₂ f with
      | Success rf =>
          args' <- monad_map (tsl_rec fuel E Σ Γ₁ Γ₂) args ;;
          ret (mkRes (tApp (trad rf) (List.map trad args'))
                    (tApp (w rf) (List.flat_map (fun (p : term * TslRes) => 
                              [tsl_rec0 0 2 (fst p); tsl_rec0 0 1 (trad (snd p)); w (snd p)]) (zip args args'))))
      | Error _ =>
          match infer' Σ Γ₁ t with
          | Checked typ =>
              typ' <- tsl_rec fuel E Σ Γ₁ Γ₂ typ ;;
              ret (mkRes (tApp univ_transport [ typ; trad typ'; UR_equiv (w typ') ; t ])
                  (tApp ur_refl [ typ; trad typ'; w typ'; t ]))
              
          | TypeError t => Error TranslationNotHandeled
          end
      end

	| _ => ret (mkRes t todo)
  end
  end.

Close Scope type_scope.


Inductive ResultType := Term | Witness.

Definition convert {A} (E : tsl_table) (t : ResultType) (x : A) :=
  p <- tmQuoteRec x;;

  match p with
  | (env, term) =>
    match infer' (empty_ext env) [] term with
    | Checked typ =>
      result <- tmEval lazy (tsl_rec fuel E (empty_ext env) [] [] term) ;;
      result' <- tmEval lazy (tsl_rec fuel E (empty_ext env) [] [] typ) ;;
      match result, result' with
      | Error e, _ | _, Error e =>
        print_nf e ;;
        fail_nf "Translation failed"

      | Success res, Success res' =>
          tmPrint "obtained translation: " ;;
          t <- tmEval all (match t with Term => trad res | Witness => (w res) end);;
          tmUnquote t >>= tmPrint
      end
    | TypeError t => fail_nf "Translation failed"
    end
  end.

Open Scope type_scope.


Definition nat_N_tsl : tsl_table :=
	[ (IndRef (mkInd "Coq.Init.Datatypes.nat" 0), mkRes <% N %> (H4CK <% compat_nat_N %>))
  ; (ConstructRef (mkInd "Coq.Init.Datatypes.nat" 0) 0, mkRes <% 0%N %> (H4CK <% compat_zero %>))
  ; (ConstRef "Coq.Init.Nat.add", mkRes <% N.add %> (H4CK <% compat_add %>))
  ; (ConstRef "Coq.Init.Nat.mul", mkRes <% N.mul %> (H4CK <% compat_mul %>))
  ; (ConstRef "Coq.Init.Nat.div", mkRes <% N.div %> (H4CK <% compat_div %>))
  ; (ConstRef "Coq.Init.Nat.pow", mkRes <% N.pow %> (H4CK <% compat_pow %>))
  ; (ConstRef "Coq.Init.Nat.sub", mkRes <% N.sub %> (H4CK <% compat_sub %>))
  ; (ConstRef "Coq.Init.Peano.le", mkRes <% N.le %> (H4CK <% compat_le  %>))
  ].


Close Scope type_scope.
Unset Strict Unquote Universe Mode.

Run TemplateProgram (convert nat_N_tsl Witness (5 + 0)).
Run TemplateProgram (convert nat_N_tsl Witness (0 + 0 - 0)).

Run TemplateProgram (convert nat_N_tsl Term    (fun (x:nat) => x * x)).
Run TemplateProgram (convert nat_N_tsl Witness (fun (x:nat) => x * x)).

Run TemplateProgram (convert nat_N_tsl Term (fun (x:nat) => pow x 2 + 2 * x + 1)).
Run TemplateProgram (convert nat_N_tsl Witness (fun (x:nat) => pow x 2 + 2 * x + 1)).

Run TemplateProgram (convert nat_N_tsl Witness (fun (x:nat) => x + 3)).
