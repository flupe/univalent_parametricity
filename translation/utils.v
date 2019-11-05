From MetaCoq Require Import Template.All Checker.All Template.Universes.
Import Template.Universes.Level.
From MetaCoq.Translations Require Import translation_utils.
Import String MonadNotation List Lists.List.ListNotations.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.


Open Scope string_scope.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

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


Fixpoint zip {A B : Type} (ta : Datatypes.list A) (tb : Datatypes.list B) : Datatypes.list (A * B) :=
  match ta, tb with
  | a :: ta, b :: tb => (a, b) :: zip ta tb
  | _, _ => []
  end.


(* HACK AHEAD *)
Fixpoint H4CK (a : term) :=
  match a with
  | tConst n u => tConst n (List.map (fun x => lSet) u)
  | tApp f args => tApp (H4CK f) (List.map H4CK args)
  | tLambda n A B => tLambda n (H4CK A) (H4CK B)
  | _ => a
  end.


(* Utilities to provide correct by construction translation rules *)
Arguments existT {_ _} _ _.
Definition type_subst := { A : Type & { B : Type & A ⋈ B }}.
Definition term_subst := { A : Type & { B : Type & { w : UR A B & { a : A & {b : B & a ≈ b }}}}}.

Definition subst_type {A B : Type} (ur : A ⋈ B) : type_subst := existT A (existT B ur).
Definition subst_term {A B : Type} {w : UR A B} {a : A} {b : B} (e : @ur A B w a b) : term_subst :=
  existT A (existT B (existT w (existT a (existT b e)))).


Definition to_global_ref (t : term) : option global_reference :=
  match t with
  | tInd ind _ => ret (IndRef ind)
  | tConstruct ind i _ => ret (ConstructRef ind i)
  | tConst n _ => ret (ConstRef n)
  | _ => None
  end.

Close Scope string_scope.

Fixpoint extract_type_rules (t : Datatypes.list type_subst) : TemplateMonad tsl_table :=
  match t with
  | [] => ret []
  | (existT A (existT B ur)) :: t =>
      A  <- tmQuote A ;;
      B  <- tmQuote B ;;
      ur <- tmQuote ur ;;
      rest <- extract_type_rules t ;;
      tmEval lazy (with_default rest (option_map (fun gr => (gr, mkRes B (H4CK ur)) :: rest) (to_global_ref A)))
  end.


Fixpoint extract_term_rules (t : Datatypes.list term_subst) : TemplateMonad tsl_table :=
  match t with
  | [] => ret []
  | (existT _ (existT _ (existT _ (existT a (existT b e))))):: t =>
      a <- tmQuote a ;;
      b <- tmQuote b ;;
      e <- tmQuote e ;;
      rest <- extract_term_rules t ;;
      tmEval lazy (with_default rest (option_map (fun gr => (gr, mkRes b (H4CK e)) :: rest) (to_global_ref a)))
  end.

Open Scope pair_scope.

Definition define_translation (n : ident)
                              (type_rules : Datatypes.list type_subst)
                              (term_rules : Datatypes.list term_subst) :=
  one <- extract_type_rules type_rules ;;
  two <- extract_term_rules term_rules ;;
  table <- tmEval all (([] : global_env), one ++ two) ;;
  tmDefinition n table.