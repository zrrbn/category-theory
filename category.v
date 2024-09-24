Class Category (Obj : Type) (Morph : Obj -> Obj -> Type) := {
  id : forall {A : Obj}, Morph A A;
  comp : forall {A B C : Obj}, Morph B C -> Morph A B -> Morph A C;

  comp_assoc : forall {A B C D : Obj} (f : Morph C D) (g : Morph B C) (h : Morph A B),
    comp f (comp g h) = comp (comp f g) h;

  id_l : forall {A B : Obj} (f : Morph A B), comp id f = f;

  id_r : forall {A B : Obj} (f : Morph A B), comp f id = f
}.

Infix "∘" := comp (at level 40, left associativity).

Definition Isomorphism {Obj : Type} {Morph : Obj -> Obj -> Type} (C : Category Obj Morph)
  {A B : Obj} (f : Morph A B) : Prop :=
  exists (g : Morph B A), g ∘ f = @id Obj Morph C A /\ f ∘ g = @id Obj Morph C B.

Definition Monomorphism {Obj : Type} {Morph : Obj -> Obj -> Type} (C : Category Obj Morph)
  {A B : Obj} (f : Morph A B) : Prop :=
  forall (X : Obj) (g1 g2 : Morph X A), f ∘ g1 = f ∘ g2 -> g1 = g2.

Definition Epimorphism {Obj : Type} {Morph : Obj -> Obj -> Type} (C : Category Obj Morph)
  {A B : Obj} (f : Morph A B) : Prop :=
  forall (Y : Obj) (h1 h2 : Morph B Y), h1 ∘ f = h2 ∘ f -> h1 = h2.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.FunctionalExtensionality.
Class Poset (A : Type) := {
    le : relation A;
    le_refl : Reflexive le;
    le_trans : Transitive le;
    le_antisym : Antisymmetric A eq le
}.

Require Import Coq.Logic.ProofIrrelevance.

Theorem poset_comp_assoc : forall {A : Type} {P : Poset A} {w x y z : A} (f : le y z) (g : le x y) (h : le w x),
le_trans w y z (le_trans w x y h g) f = 
      le_trans w x z h (le_trans x y z g f).
Proof.
  intros A P w x y z f g h.
  unfold le_trans.
  apply proof_irrelevance.
Qed.

Theorem poset_id_l : forall {A : Type} {P : Poset A} {x y : A} (f : le x y),
le_trans x y y f (le_refl y) = f.
Proof.
  intros A P x y f.
  unfold le_trans.
  apply proof_irrelevance.
Qed.

Theorem poset_id_r : forall {A : Type} {P : Poset A} {x y : A} (f : le x y),
le_trans x x y (le_refl x) f = f.
Proof.
  intros A P x y f.
  unfold le_trans.
  apply proof_irrelevance.
Qed.

Instance Poset_Cat {A : Type} (P : Poset A) : Category A (fun x y => le x y) := {
  id := fun x => le_refl x;

  comp := fun x y z (f : le y z) (g : le x y) => le_trans x y z g f;

  comp_assoc := fun x y z w f g h => poset_comp_assoc f g h;

  id_l := fun x y f => poset_id_l f;

  id_r := fun x y f => poset_id_r f
}.