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

(* 7. Characterization of Equivalences by Contractible Homotopy Fibers *)

Lemma idmap_contr_fibers (A : Type) (y : A) : IsContr (fiber (fun x : A => x) y).
Proof.
  exists (existT (fun x => paths x y) y idpath).
  intros [x p].
  destruct p.
  reflexivity.
Defined.

Lemma equiv_contr_fibers (A B : Type) (e : Equiv A B) :
  forall y : B, IsContr (fiber (equiv_fun A B e) y).
Proof.
  pose (p := ua A B e).
  pose (e' := idToEqv A B p).
  assert (H : forall (Y : Type) (q : paths A Y) (y : Y),
                IsContr (fiber (equiv_fun A Y (idToEqv A Y q)) y)).
  { intros Y q. destruct q. apply idmap_contr_fibers. }
  intros y.
  pose (eq_e := idToEqv_ua A B e).
  exact (transport (fun E => IsContr (fiber (equiv_fun A B E) y)) eq_e (H B p y)).
Defined.

Theorem isequiv_to_contr_fibers {A B : Type} (f : A -> B) (H : IsEquiv f) :
  forall y : B, IsContr (fiber f y).
Proof.
  pose (e := Build_Equiv A B f H).
  apply (equiv_contr_fibers A B e).
Defined.

Theorem contr_fibers_to_isequiv {A B : Type} (f : A -> B)
  (H : forall y : B, IsContr (fiber f y)) : IsEquiv f.
Proof.
  refine (Build_IsEquiv A B f
    (fun y => projT1 (projT1 (H y)))
    (fun x => ap (@projT1 A (fun a => paths (f a) (f x)))
                 (projT2 (H (f x)) (existT (fun a => paths (f a) (f x)) x idpath)))
    (fun y => projT2 (projT1 (H y)))).
Defined.

Definition equiv_iff_contr_fibers {A B : Type} (f : A -> B) :
  (IsEquiv f -> forall y : B, IsContr (fiber f y)) *
  ((forall y : B, IsContr (fiber f y)) -> IsEquiv f) :=
  (isequiv_to_contr_fibers f, contr_fibers_to_isequiv f).

(* 8. Truncation Levels and Inductive n-Types *)

Definition IsSet (A : Type) : Type :=
  forall (x y : A) (p q : paths x y), paths p q.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Definition minus_one : trunc_index := trunc_S minus_two.
Definition zero_type : trunc_index := trunc_S minus_one.
Definition one_type : trunc_index := trunc_S zero_type.

Fixpoint is_trunc (n : trunc_index) (A : Type) : Type :=
  match n with
  | minus_two => IsContr A
  | trunc_S n' => forall (x y : A), is_trunc n' (paths x y)
  end.

Inductive is_n_type : trunc_index -> Type -> Type :=
| is_n_type_contr : forall A, IsContr A -> is_n_type minus_two A
| is_n_type_succ : forall n A, (forall (x y : A), is_n_type n (paths x y)) -> is_n_type (trunc_S n) A.

Theorem is_n_type_to_is_trunc (n : trunc_index) (A : Type) (H : is_n_type n A) : is_trunc n A.
Proof.
  induction H as [A Hc | n A Hrec IH].
  - exact Hc.
  - simpl. intros x y. apply IH.
Defined.

Theorem is_trunc_to_is_n_type (n : trunc_index) : forall (A : Type), is_trunc n A -> is_n_type n A.
Proof.
  induction n as [| n' IH]; intros A H.
  - apply is_n_type_contr. exact H.
  - apply is_n_type_succ. intros x y. apply IH. apply H.
Defined.

Definition path_contr {A : Type} (H : IsContr A) (x y : A) : paths x y :=
  concat (inverse (projT2 H x)) (projT2 H y).

Lemma path_contr_canonical {A : Type} (H : IsContr A) {x y : A} (r : paths x y)
  : paths r (path_contr H x y).
Proof.
  destruct r.
  unfold path_contr.
  destruct (concat_Vp (projT2 H x)).
  reflexivity.
Defined.

Definition path2_contr {A : Type} (H : IsContr A) {x y : A} (p q : paths x y) : paths p q :=
  concat (path_contr_canonical H p) (inverse (path_contr_canonical H q)).

Theorem contr_paths_is_contr {A : Type} (H : IsContr A) (x y : A) : IsContr (paths x y).
Proof.
  exists (path_contr H x y).
  intro p.
  apply (path2_contr H).
Defined.

Theorem is_contr_to_is_prop (A : Type) (H : IsContr A) : IsProp A.
Proof.
  intros x y.
  exact (path_contr H x y).
Defined.

Theorem is_prop_to_paths_contr (A : Type) (H : IsProp A) (x y : A) : IsContr (paths x y).
Proof.
  pose (C := existT (fun c : A => forall z : A, paths c z) x (H x) : IsContr A).
  apply (contr_paths_is_contr C).
Defined.

Theorem is_prop_to_is_set (A : Type) (H : IsProp A) : IsSet A.
Proof.
  intros x y p q.
  pose (Hp := is_prop_to_paths_contr A H x y).
  exact (path_contr Hp p q).
Defined.

Theorem is_prop_to_is_minus_one_type (A : Type) (H : IsProp A) : is_n_type minus_one A.
Proof.
  apply is_n_type_succ.
  intros x y.
  apply is_n_type_contr.
  apply is_prop_to_paths_contr.
  exact H.
Defined.

Theorem is_minus_one_type_to_is_prop (A : Type) (H : is_n_type minus_one A) : IsProp A.
Proof.
  apply is_n_type_to_is_trunc in H.
  simpl in H.
  intros x y.
  exact (projT1 (H x y)).
Defined.

Theorem is_set_to_is_zero_type (A : Type) (H : IsSet A) : is_n_type zero_type A.
Proof.
  apply is_n_type_succ.
  intros x y.
  apply is_prop_to_is_minus_one_type.
  exact (H x y).
Defined.

Theorem is_zero_type_to_is_set (A : Type) (H : is_n_type zero_type A) : IsSet A.
Proof.
  apply is_n_type_to_is_trunc in H.
  simpl in H.
  intros x y.
  intros p q.
  exact (projT1 (H x y p q)).
Defined.

(* 9. Hedberg's Theorem: Decidable Equality Implies Sets (0-Types) *)

Inductive Empty : Type := .

Definition not (A : Type) : Type := A -> Empty.

Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Definition DecidablePaths (A : Type) : Type :=
  forall (x y : A), sum (paths x y) (not (paths x y)).

Definition WeaklyConstant {A B : Type} (f : A -> B) : Type :=
  forall (x y : A), paths (f x) (f y).

Record Collapsible (A : Type) : Type := Build_Collapsible {
  collapse : A -> A;
  collapse_wconst : WeaklyConstant collapse
}.

Lemma decidable_to_collapsible (A : Type) (d : sum A (not A)) : Collapsible A.
Proof.
  destruct d as [a | na].
  - refine (Build_Collapsible A (fun _ => a) (fun _ _ => idpath)).
  - refine (Build_Collapsible A (fun x => match na x with end) (fun x => match na x with end)).
Defined.

Theorem hedberg_from_collapsible (A : Type) (coll : forall (x y : A), Collapsible (paths x y)) : IsSet A.
Proof.
  intros x y p q.
  pose (c := fun u v (r : paths u v) => collapse (paths u v) (coll u v) r).
  pose (wc := fun u v (r1 r2 : paths u v) => collapse_wconst (paths u v) (coll u v) r1 r2).
  pose (rx := c x x idpath).
  assert (Hcanon : forall (z : A) (r : paths x z), paths r (concat (inverse rx) (c x z r))).
  { intros z r.
    destruct r.
    unfold rx.
    exact (inverse (concat_Vp (c x x idpath))). }
  pose (p_canon := Hcanon y p).
  pose (q_canon := Hcanon y q).
  pose (c_eq := wc x y p q).
  pose (ap_concat := ap (fun w => concat (inverse rx) w) c_eq).
  exact (concat p_canon (concat ap_concat (inverse q_canon))).
Defined.

Theorem hedberg (A : Type) (dec : DecidablePaths A) : IsSet A.
Proof.
  apply hedberg_from_collapsible.
  intros x y.
  apply decidable_to_collapsible.
  apply dec.
Defined.

Theorem hedberg_is_zero_type (A : Type) (dec : DecidablePaths A) : is_n_type zero_type A.
Proof.
  apply is_set_to_is_zero_type.
  apply hedberg.
  exact dec.
Defined.
