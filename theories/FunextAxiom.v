(** To assume the Funext axiom outright, import this file.
    (Doing this instead of simply positing Funext directly
    avoids creating multiple witnesses for the axiom in
    different developments.) *)

Require Import Basics.Overture.
Require Import FunextVarieties.

Axiom funext_axiom : Funext.
Global Existing Instance funext_axiom.

(** Unified Function Extensionality Bridges (Ticket 7433 / Issue 34) *)

Definition funext_to_type : Funext_type := fun A P f g => isequiv_apD10 A P f g.

Definition funext_to_naive_funext : NaiveFunext
  := Funext_implies_NaiveFunext funext_to_type.

Definition funext_to_weak_funext : WeakFunext
  := NaiveFunext_implies_WeakFunext funext_to_naive_funext.

Definition weak_funext_to_funext : WeakFunext -> Funext_type
  := WeakFunext_implies_Funext.

Definition naive_funext_to_funext : NaiveFunext -> Funext_type
  := NaiveFunext_implies_Funext.

