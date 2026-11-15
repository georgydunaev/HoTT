(** To assume the Univalence axiom outright, import this file.
    (Doing this instead of simply positing Univalence directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import Types.Universe.
Require Import UnivalenceVarieties UnivalenceImpliesFunext.

Axiom univalence_axiom : Univalence.
Global Existing Instance univalence_axiom.

(** Unified Univalence and Function Extensionality Bridges (Ticket 7433 / Issue 34) *)

Definition univalence_to_type : Univalence_type
  := fun A B => isequiv_equiv_path A B.

Definition weak_univalence_to_univalence : WeakUnivalence -> Univalence_type
  := WeakUnivalence_implies_Univalence.

Definition incoherent_weak_univalence_to_univalence `{Funext}
  : IncoherentWeakUnivalence -> Univalence_type
  := IncoherentWeakUnivalence_implies_Univalence.

Definition very_weak_univalence_to_univalence `{Funext}
  : VeryWeakUnivalence -> Univalence_type
  := VeryWeakUnivalence_implies_Univalence.

Global Instance univalence_implies_funext_instance : Funext
  := Univalence_implies_Funext univalence_axiom.

