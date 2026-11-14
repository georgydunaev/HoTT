(**
  Auto-generated formal theory for HoTT repository.
  Source: Homotopy Type Theory, Voevodsky's Univalence Axiom,
          Function Extensionality, and Propositional Extensionality.
  Regeneration command: coqc -indices-matter theories/Univalence.v
*)

Set Universe Polymorphism.

(* 1. Identity System and Path Induction Principles *)

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Definition J {A : Type} {a : A} (P : forall (b : A), paths a b -> Type)
  (d : P a idpath) {b : A} (p : paths a b) : P b p :=
  match p with
  | idpath => d
  end.

Definition based_path_induction {A : Type} (a : A)
  (P : forall (x : A), paths a x -> Type)
  (d : P a idpath) {x : A} (p : paths a x) : P x p :=
  match p with
  | idpath => d
  end.

Definition concat {A : Type} {x y z : A} (p : paths x y) (q : paths y z) : paths x z :=
  match q with
  | idpath => p
  end.

Definition inverse {A : Type} {x y : A} (p : paths x y) : paths y x :=
  match p with
  | idpath => idpath
  end.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : paths x y) : paths (f x) (f y) :=
  match p with
  | idpath => idpath
  end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : paths x y) (u : P x) : P y :=
  match p with
  | idpath => u
  end.

(* Homotopy Groupoid Laws *)

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

(* 2. Homotopies, Fibers, Contractibility, and Equivalences *)

Definition Homotopy {A B : Type} (f g : A -> B) : Type :=
  forall (x : A), paths (f x) (g x).

Definition fiber {A B : Type} (f : A -> B) (y : B) : Type :=
  { x : A & paths (f x) y }.

Definition IsContr (A : Type) : Type :=
  { c : A & forall (x : A), paths c x }.

Record IsEquiv {A B : Type} (f : A -> B) : Type := Build_IsEquiv {
  equiv_inv : B -> A;
  eissect : Homotopy (fun x => equiv_inv (f x)) (fun x => x);
  eisretr : Homotopy (fun y => f (equiv_inv y)) (fun y => y)
}.

Record Equiv (A B : Type) : Type := Build_Equiv {
  equiv_fun : A -> B;
  equiv_isequiv : IsEquiv equiv_fun
}.

Theorem isequiv_idmap (A : Type) : IsEquiv (fun (x : A) => x).
Proof.
  refine (Build_IsEquiv A A (fun x => x) (fun x => x) (fun x => idpath) (fun x => idpath)).
Defined.

Definition equiv_idmap (A : Type) : Equiv A A :=
  Build_Equiv A A (fun x => x) (isequiv_idmap A).

Definition contr_retract {A B : Type} (r : A -> B) (s : B -> A)
  (H_rs : forall (b : B), paths (r (s b)) b) (H_A : IsContr A) : IsContr B.
Proof.
  exists (r (projT1 H_A)).
  intro b.
  refine (concat _ (H_rs b)).
  apply ap.
  apply (projT2 H_A).
Defined.

(* 3. Map from Path to Equivalence *)

Definition idtoeqv (A B : Type) (p : paths A B) : Equiv A B :=
  match p with
  | idpath => equiv_idmap A
  end.

(* 4. Voevodsky's Univalence Axiom *)

Definition Univalence_Statement : Type :=
  forall (A B : Type), IsEquiv (idtoeqv A B).

Axiom univalence_axiom : Univalence_Statement.

Definition ua (A B : Type) (e : Equiv A B) : paths A B :=
  equiv_inv (idtoeqv A B) (univalence_axiom A B) e.

Theorem ua_idtoeqv (A B : Type) (p : paths A B) : paths (ua A B (idtoeqv A B p)) p.
Proof.
  apply (eissect (idtoeqv A B) (univalence_axiom A B)).
Defined.

Theorem idtoeqv_ua (A B : Type) (e : Equiv A B) : paths (idtoeqv A B (ua A B e)) e.
Proof.
  apply (eisretr (idtoeqv A B) (univalence_axiom A B)).
Defined.

(* 5. Univalence Consequence 1: Equivalence between Paths and Equivalences *)

Definition eqtoequiv_is_equiv (A B : Type) : Equiv (paths A B) (Equiv A B) :=
  Build_Equiv (paths A B) (Equiv A B) (idtoeqv A B) (univalence_axiom A B).

(* 6. Univalence Consequence 2: Constructive Derivation of Function Extensionality *)

Theorem isequiv_postcompose (C : Type) {A B : Type} (e : Equiv A B)
  : IsEquiv (fun (g : C -> A) => fun (x : C) => equiv_fun A B e (g x)).
Proof.
  pose (p := ua A B e).
  pose (eq_e := idtoeqv_ua A B e).
  assert (H : forall (Y : Type) (q : paths A Y),
            IsEquiv (fun (g : C -> A) => fun (x : C) => equiv_fun A Y (idtoeqv A Y q) (g x))).
  { intros Y q. destruct q. apply isequiv_idmap. }
  exact (transport (fun E => IsEquiv (fun (g : C -> A) => fun (x : C) => equiv_fun A B E (g x))) eq_e (H B p)).
Defined.

Lemma idmap_contr_fibers (A : Type) (y : A) : IsContr (fiber (fun x : A => x) y).
Proof.
  exists (existT (fun x => paths x y) y idpath).
  intros [x p].
  destruct p.
  reflexivity.
Defined.

Theorem isequiv_to_contr_fibers {A B : Type} (f : A -> B) (Hf : IsEquiv f) (y : B)
  : IsContr (fiber f y).
Proof.
  pose (e := Build_Equiv A B f Hf).
  pose (p := ua A B e).
  assert (H : forall (Y : Type) (q : paths A Y) (y0 : Y),
                IsContr (fiber (equiv_fun A Y (idtoeqv A Y q)) y0)).
  { intros Y q. destruct q. apply idmap_contr_fibers. }
  pose (eq_e := idtoeqv_ua A B e).
  exact (transport (fun E => IsContr (fiber (equiv_fun A B E) y)) eq_e (H B p y)).
Defined.

Definition isequiv_pr1 {X : Type} (P : X -> Type) (H : forall x : X, IsContr (P x))
  : IsEquiv (@projT1 X P).
Proof.
  refine (Build_IsEquiv {x : X & P x} X (@projT1 X P)
            (fun x => existT P x (projT1 (H x)))
            _
            (fun x => idpath)).
  intros [x p].
  simpl.
  pose (q := projT2 (H x) p).
  destruct q.
  reflexivity.
Defined.

Definition happly {A : Type} {B : A -> Type} {f g : forall x : A, B x} (p : paths f g)
  : forall x : A, paths (f x) (g x) :=
  fun x => match p with idpath => idpath end.

Theorem weak_funext {X : Type} (P : X -> Type) (H : forall x : X, IsContr (P x))
  : IsContr (forall x : X, P x).
Proof.
  pose (eq_pr1 := Build_Equiv {x : X & P x} X (@projT1 X P) (isequiv_pr1 P H)).
  pose (eq_post := isequiv_postcompose X eq_pr1).
  pose (T := fiber (fun g : X -> {x : X & P x} => fun x => projT1 (g x)) (fun x => x)).
  pose (contr_T := isequiv_to_contr_fibers _ eq_post (fun x => x)).
  pose (r := fun (fp : T) (x : X) =>
               transport P (happly (projT2 fp) x) (projT2 (projT1 fp x))).
  pose (s := fun (f : forall x : X, P x) =>
               existT (fun g : X -> {x : X & P x} => paths (fun x => projT1 (g x)) (fun x => x))
                      (fun x => existT P x (f x))
                      idpath).
  apply (contr_retract r s (fun f => idpath) contr_T).
Defined.

Theorem funext_dep {A : Type} {B : A -> Type} (f g : forall x : A, B x)
  (H : forall x : A, paths (f x) (g x)) : paths f g.
Proof.
  pose (T_x := fun x : A => { y : B x & paths (f x) y }).
  assert (contr_Tx : forall x : A, IsContr (T_x x)).
  {
    intro x.
    exists (existT (fun y => paths (f x) y) (f x) idpath).
    intros [y p].
    destruct p.
    reflexivity.
  }
  pose (contr_pi := weak_funext T_x contr_Tx).
  pose (k0 := fun x : A => existT (fun y => paths (f x) y) (f x) idpath).
  pose (k1 := fun x : A => existT (fun y => paths (f x) y) (g x) (H x)).
  pose (p_k := concat (inverse (projT2 contr_pi k0)) (projT2 contr_pi k1)).
  pose (retract_T := { h : forall x : A, B x & forall x : A, paths (f x) (h x) }).
  pose (r := fun (k : forall x : A, T_x x) =>
               existT (fun h => forall x : A, paths (f x) (h x))
                      (fun x => projT1 (k x))
                      (fun x => projT2 (k x))).
  pose (p_r := ap r p_k).
  exact (ap (@projT1 (forall x : A, B x) (fun h => forall x : A, paths (f x) (h x))) p_r).
Defined.

Theorem funext_nondep {A B : Type} (f g : A -> B)
  (H : forall x : A, paths (f x) (g x)) : paths f g.
Proof.
  apply (funext_dep f g H).
Defined.

(* 7. Univalence Consequence 3: Equivalence of Propositions is Equality of Propositions *)

Definition IsProp (A : Type) : Type :=
  forall (x y : A), paths x y.

Theorem prop_equiv_to_id (A B : Type) (pA : IsProp A) (pB : IsProp B)
  (f : A -> B) (g : B -> A) : paths A B.
Proof.
  assert (H_eq : IsEquiv f).
  {
    refine (Build_IsEquiv A B f g _ _).
    - intro x. apply pA.
    - intro y. apply pB.
  }
  pose (e := Build_Equiv A B f H_eq).
  exact (ua A B e).
Defined.

Theorem is_prop_equiv_is_id (A B : Type) (pA : IsProp A) (pB : IsProp B)
  (iff : (A -> B) * (B -> A)) : paths A B.
Proof.
  destruct iff as [f g].
  apply (prop_equiv_to_id A B pA pB f g).
Defined.
