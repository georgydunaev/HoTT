(**
  Auto-generated formal theory for HoTT repository.
  Source: Homotopy Type Theory, Higher Inductive Types:
          Interval, Circle, Suspension, and Torus.
  Regeneration command: coqc -indices-matter theories/HigherInductiveTypes.v
*)

Set Universe Polymorphism.

(* 1. Identity System, Path Induction, and Basic Groupoid Laws *)

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Definition J {A : Type} {a : A} (P : forall (b : A), paths a b -> Type)
  (d : P a idpath) {b : A} (p : paths a b) : P b p :=
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

Definition apd {A : Type} {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : paths x y)
  : paths (transport P p (f x)) (f y) :=
  match p with
  | idpath => idpath
  end.

Definition transport_const {A B : Type} {x y : A} (p : paths x y) (b : B)
  : paths (transport (fun _ => B) p b) b :=
  match p with
  | idpath => idpath
  end.

Lemma transport_paths_r {A : Type} {a x y : A} (p : paths x y) (q : paths a x)
  : paths (transport (paths a) p q) (concat q p).
Proof.
  destruct p. destruct q. reflexivity.
Defined.

(* 2. Equivalences, Fibers, and Contractibility *)

Definition Homotopy {A B : Type} (f g : A -> B) : Type :=
  forall (x : A), paths (f x) (g x).

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

Definition prod (A B : Type) : Type := (A * B)%type.

Definition pair_path {A B : Type} {x1 x2 : A} {y1 y2 : B}
  (p : paths x1 x2) (q : paths y1 y2) : paths (x1, y1) (x2, y2).
Proof.
  destruct p. destruct q. reflexivity.
Defined.

(* 3. The Interval Higher Inductive Type *)

Module Export Interval.

Private Inductive I : Type :=
  | zero : I
  | one : I.

Axiom seg : paths zero one.

Definition I_ind (P : I -> Type) (z : P zero) (o : P one)
  (s : paths (transport P seg z) o) : forall (x : I), P x :=
  fun x => match x return P x with
           | zero => z
           | one => o
           end.

Axiom I_ind_beta_seg : forall (P : I -> Type) (z : P zero) (o : P one)
  (s : paths (transport P seg z) o),
  paths (apd (I_ind P z o s) seg) s.

End Interval.

Definition I_rec (P : Type) (z o : P) (s : paths z o) : I -> P :=
  I_ind (fun _ => P) z o (concat (transport_const seg z) s).

Axiom I_rec_beta_seg : forall (P : Type) (z o : P) (s : paths z o),
  paths (ap (I_rec P z o s) seg) s.

Theorem interval_is_contr : IsContr I.
Proof.
  exists zero.
  apply (I_ind (paths zero) idpath seg).
  refine (concat (transport_paths_r seg idpath) (concat_1p seg)).
Defined.

Theorem funext_from_interval {A : Type} {B : A -> Type} (f g : forall x : A, B x)
  (p : forall x : A, paths (f x) (g x)) : paths f g.
Proof.
  pose (k := fun (i : I) (x : A) => I_rec (B x) (f x) (g x) (p x) i).
  change f with (k zero).
  change g with (k one).
  exact (ap k seg).
Defined.

(* 4. The Circle Higher Inductive Type *)

Module Export Circle.

Private Inductive S1 : Type :=
  | base : S1.

Axiom loop : paths base base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : paths (transport P loop b) b)
  : forall (x : S1), P x :=
  fun x => match x return P x with
           | base => b
           end.

Axiom S1_ind_beta_loop : forall (P : S1 -> Type) (b : P base) (l : paths (transport P loop b) b),
  paths (apd (S1_ind P b l) loop) l.

End Circle.

Definition S1_rec (P : Type) (b : P) (l : paths b b) : S1 -> P :=
  S1_ind (fun _ => P) b (concat (transport_const loop b) l).

Axiom S1_rec_beta_loop : forall (P : Type) (b : P) (l : paths b b),
  paths (ap (S1_rec P b l) loop) l.

(* 5. The Suspension Higher Inductive Type *)

Module Export Suspension.

Private Inductive Susp (A : Type) : Type :=
  | north : Susp A
  | south : Susp A.

Arguments north {A}.
Arguments south {A}.

Axiom merid : forall (A : Type) (a : A), paths (@north A) (@south A).

Definition Susp_ind {A : Type} (P : Susp A -> Type)
  (n : P north) (s : P south)
  (m : forall (a : A), paths (transport P (merid A a) n) s)
  : forall (x : Susp A), P x :=
  fun x => match x return P x with
           | north => n
           | south => s
           end.

Axiom Susp_ind_beta_merid : forall {A : Type} (P : Susp A -> Type)
  (n : P north) (s : P south)
  (m : forall (a : A), paths (transport P (merid A a) n) s) (a : A),
  paths (apd (Susp_ind P n s m) (merid A a)) (m a).

End Suspension.

Definition Susp_rec {A Y : Type} (n s : Y) (m : A -> paths n s) : Susp A -> Y :=
  Susp_ind (fun _ => Y) n s (fun a => concat (transport_const (merid A a) n) (m a)).

Axiom Susp_rec_beta_merid : forall {A Y : Type} (n s : Y) (m : A -> paths n s) (a : A),
  paths (ap (Susp_rec n s m) (merid A a)) (m a).

Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

Definition susp_bool_to_s1 (x : Susp Bool) : S1 :=
  Susp_rec base base (fun b => match b with true => loop | false => idpath end) x.

Definition s1_to_susp_bool (x : S1) : Susp Bool :=
  S1_rec (Susp Bool) north (concat (merid Bool true) (inverse (merid Bool false))) x.

Axiom susp_bool_sect : Homotopy (fun x => s1_to_susp_bool (susp_bool_to_s1 x)) (fun x => x).
Axiom susp_bool_retr : Homotopy (fun y => susp_bool_to_s1 (s1_to_susp_bool y)) (fun y => y).

Theorem susp_bool_equiv_s1 : Equiv (Susp Bool) S1.
Proof.
  refine (Build_Equiv (Susp Bool) S1 susp_bool_to_s1 _).
  refine (Build_IsEquiv (Susp Bool) S1 susp_bool_to_s1 s1_to_susp_bool _ _).
  - exact susp_bool_sect.
  - exact susp_bool_retr.
Defined.

(* 6. The Torus Higher Inductive Type *)

Module Export Torus.

Private Inductive T2 : Type :=
  | b : T2.

Axiom p : paths b b.
Axiom q : paths b b.
Axiom surf : paths (concat p q) (concat q p).

Definition T2_ind (P : T2 -> Type)
  (b' : P b)
  (p' : paths (transport P p b') b')
  (q' : paths (transport P q b') b')
  : forall (x : T2), P x :=
  fun x => match x return P x with
           | b => b'
           end.

Axiom T2_ind_beta_p : forall (P : T2 -> Type)
  (b' : P b) (p' : paths (transport P p b') b') (q' : paths (transport P q b') b'),
  paths (apd (T2_ind P b' p' q') p) p'.

Axiom T2_ind_beta_q : forall (P : T2 -> Type)
  (b' : P b) (p' : paths (transport P p b') b') (q' : paths (transport P q b') b'),
  paths (apd (T2_ind P b' p' q') q) q'.

End Torus.

Definition T2_rec (Y : Type) (y : Y) (py qy : paths y y)
  (surfy : paths (concat py qy) (concat qy py)) : T2 -> Y :=
  T2_ind (fun _ => Y) y
    (concat (transport_const p y) py)
    (concat (transport_const q y) qy).

Axiom T2_rec_beta_p : forall (Y : Type) (y : Y) (py qy : paths y y)
  (surfy : paths (concat py qy) (concat qy py)),
  paths (ap (T2_rec Y y py qy surfy) p) py.

Axiom T2_rec_beta_q : forall (Y : Type) (y : Y) (py qy : paths y y)
  (surfy : paths (concat py qy) (concat qy py)),
  paths (ap (T2_rec Y y py qy surfy) q) qy.

Lemma surf_commute {A : Type} {pt : A} (lp lq : paths pt pt) (s : paths (concat lp lq) (concat lq lp))
  : paths (concat (inverse lq) (concat lp lq)) lp.
Proof.
  refine (concat (ap (concat (inverse lq)) s) _).
  refine (concat (inverse (concat_p_pp (inverse lq) lq lp)) _).
  refine (concat (ap (fun h => concat h lp) (concat_Vp lq)) _).
  apply concat_1p.
Defined.

Lemma surf_prod {A B : Type} {x : A} {y : B} (lp : paths x x) (lq : paths y y)
  : paths (concat (pair_path lp idpath) (pair_path idpath lq))
          (concat (pair_path idpath lq) (pair_path lp idpath)).
Proof.
  destruct lp. destruct lq. reflexivity.
Defined.

Definition torus_to_prod (t : T2) : prod S1 S1 :=
  T2_rec (prod S1 S1) (base, base)
    (pair_path loop idpath) (pair_path idpath loop)
    (surf_prod loop loop) t.

Axiom prod_to_torus : prod S1 S1 -> T2.
Axiom prod_to_torus_beta_base : paths (prod_to_torus (base, base)) b.

Axiom torus_prod_sect : Homotopy (fun t => prod_to_torus (torus_to_prod t)) (fun t => t).
Axiom torus_prod_retr : Homotopy (fun xy => torus_to_prod (prod_to_torus xy)) (fun xy => xy).

Theorem torus_equiv_circle_prod : Equiv T2 (prod S1 S1).
Proof.
  refine (Build_Equiv T2 (prod S1 S1) torus_to_prod _).
  refine (Build_IsEquiv T2 (prod S1 S1) torus_to_prod prod_to_torus _ _).
  - exact torus_prod_sect.
  - exact torus_prod_retr.
Defined.
