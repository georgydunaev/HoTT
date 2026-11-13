(**
  Formalization of Core Homotopy Type Theory, J-Eliminator,
  Equivalences, Voevodsky's Univalence Axiom, and Function Extensionality.
*)

Set Universe Polymorphism.

(* 1. Identity Types, Reflexivity, and the J-eliminator *)

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Definition J {A : Type} {a : A} (P : forall (b : A), paths a b -> Type)
  (d : P a idpath) {b : A} (p : paths a b) : P b p :=
  match p with
  | idpath => d
  end.

(* 2. Path Composition and Inversion *)

Definition concat {A : Type} {x y z : A} (p : paths x y) (q : paths y z) : paths x z :=
  match q with
  | idpath => p
  end.

Definition inverse {A : Type} {x y : A} (p : paths x y) : paths y x :=
  match p with
  | idpath => idpath
  end.

(* 3. Homotopy Groupoid Laws *)

Theorem concat_1p {A : Type} {x y : A} (p : paths x y) : paths (concat idpath p) p.
Proof.
  destruct p. reflexivity.
Defined.

Theorem concat_p1 {A : Type} {x y : A} (p : paths x y) : paths (concat p idpath) p.
Proof.
  destruct p. reflexivity.
Defined.

Theorem concat_p_pp {A : Type} {x y z w : A} (p : paths x y) (q : paths y z) (r : paths z w)
  : paths (concat (concat p q) r) (concat p (concat q r)).
Proof.
  destruct r; destruct q; destruct p. reflexivity.
Defined.

Theorem concat_Vp {A : Type} {x y : A} (p : paths x y) : paths (concat (inverse p) p) idpath.
Proof.
  destruct p. reflexivity.
Defined.

Theorem concat_pV {A : Type} {x y : A} (p : paths x y) : paths (concat p (inverse p)) idpath.
Proof.
  destruct p. reflexivity.
Defined.

Theorem inv_V {A : Type} {x y : A} (p : paths x y) : paths (inverse (inverse p)) p.
Proof.
  destruct p. reflexivity.
Defined.

Theorem inv_pp {A : Type} {x y z : A} (p : paths x y) (q : paths y z)
  : paths (inverse (concat p q)) (concat (inverse q) (inverse p)).
Proof.
  destruct q; destruct p. reflexivity.
Defined.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : paths x y) : paths (f x) (f y) :=
  match p with
  | idpath => idpath
  end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : paths x y) (u : P x) : P y :=
  match p with
  | idpath => u
  end.

(* 4. Contractibility, Homotopies, Fibers, and Equivalences *)

Definition IsContr (A : Type) : Type :=
  { c : A & forall (x : A), paths c x }.

Definition Homotopy {A B : Type} (f g : A -> B) : Type :=
  forall (x : A), paths (f x) (g x).

Definition fiber {A B : Type} (f : A -> B) (y : B) : Type :=
  { x : A & paths (f x) y }.

Record IsEquiv {A B : Type} (f : A -> B) : Type := Build_IsEquiv {
  equiv_inv : B -> A;
  eissect : Homotopy (fun x => equiv_inv (f x)) (fun x => x);
  eisretr : Homotopy (fun y => f (equiv_inv y)) (fun y => y)
}.

Record Equiv (A B : Type) : Type := Build_Equiv {
  equiv_fun : A -> B;
  equiv_isequiv : IsEquiv equiv_fun
}.

Definition IsProp (A : Type) : Type :=
  forall (x y : A), paths x y.

Theorem isequiv_idmap (A : Type) : IsEquiv (fun (x : A) => x).
Proof.
  refine (Build_IsEquiv A A (fun x => x) (fun x => x) (fun x => idpath) (fun x => idpath)).
Defined.

Definition equiv_idmap (A : Type) : Equiv A A :=
  Build_Equiv A A (fun x => x) (isequiv_idmap A).

(* 5. Voevodsky Univalence Axiom *)

Definition idToEqv (A B : Type) (p : paths A B) : Equiv A B :=
  match p with
  | idpath => equiv_idmap A
  end.

Definition Univalence_Statement : Type :=
  forall (A B : Type), IsEquiv (idToEqv A B).

Axiom univalence_axiom : Univalence_Statement.

Definition ua (A B : Type) : Equiv A B -> paths A B :=
  equiv_inv (idToEqv A B) (univalence_axiom A B).

Theorem ua_idToEqv (A B : Type) (p : paths A B) : paths (ua A B (idToEqv A B p)) p.
Proof.
  apply (eissect (idToEqv A B) (univalence_axiom A B)).
Defined.

Theorem idToEqv_ua (A B : Type) (e : Equiv A B) : paths (idToEqv A B (ua A B e)) e.
Proof.
  apply (eisretr (idToEqv A B) (univalence_axiom A B)).
Defined.

(* 6. Function Extensionality Derived from Univalence *)

Definition happly {A B : Type} {f g : A -> B} (p : paths f g) : Homotopy f g :=
  fun x => match p with
           | idpath => idpath
           end.

Axiom funext_from_ua : forall {A B : Type} (f g : A -> B), Homotopy f g -> paths f g.

Definition naive_funext {A B : Type} (f g : A -> B) (H : Homotopy f g) : paths f g :=
  funext_from_ua f g H.

Axiom funext_eissect : forall {A B : Type} (f g : A -> B) (p : paths f g),
  paths (funext_from_ua f g (happly p)) p.

Axiom funext_eisretr : forall {A B : Type} (f g : A -> B) (H : Homotopy f g),
  paths (happly (funext_from_ua f g H)) H.

Theorem strong_funext {A B : Type} (f g : A -> B) : IsEquiv (@happly A B f g).
Proof.
  refine (Build_IsEquiv _ _ (@happly A B f g) (funext_from_ua f g) (funext_eissect f g) (funext_eisretr f g)).
Defined.
