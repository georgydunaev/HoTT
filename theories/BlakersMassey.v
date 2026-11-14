(**
  Auto-generated formal theory for HoTT repository.
  Source: Homotopy Type Theory, Blakers-Massey Connectivity Theorem
          and Freudenthal Suspension Theorem.
  Regeneration command: coqc -indices-matter theories/BlakersMassey.v
*)

Set Universe Polymorphism.

(* 1. Identity System, Groupoid Operations, and Equivalences *)

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

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : paths x y) : paths (f x) (f y) :=
  match p with
  | idpath => idpath
  end.

Definition apd {A : Type} {P : A -> Type} (f : forall x : A, P x) {x y : A} (p : paths x y)
  : paths (match p in paths _ y return P y with idpath => f x end) (f y) :=
  match p with
  | idpath => idpath
  end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : paths x y) (u : P x) : P y :=
  match p with
  | idpath => u
  end.

Definition transport_const {A B : Type} {x y : A} (p : paths x y) (b : B)
  : paths (transport (fun _ => B) p b) b :=
  match p with
  | idpath => idpath
  end.

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

Definition fiber {A B : Type} (f : A -> B) (y : B) : Type :=
  { x : A & paths (f x) y }.

(* 2. Truncation Levels, Arithmetic, and Truncation Modality *)

Inductive trunc_index : Type :=
  | minus_two : trunc_index
  | trunc_S : trunc_index -> trunc_index.

Definition minus_one : trunc_index := trunc_S minus_two.
Definition zero_type : trunc_index := trunc_S minus_one.
Definition one_type : trunc_index := trunc_S zero_type.

Fixpoint trunc_index_add (m n : trunc_index) : trunc_index :=
  match m with
  | minus_two => n
  | trunc_S m' => trunc_S (trunc_index_add m' n)
  end.

Fixpoint trunc_index_leq (m n : trunc_index) : Type :=
  match m, n with
  | minus_two, _ => True
  | trunc_S m', minus_two => False
  | trunc_S m', trunc_S n' => trunc_index_leq m' n'
  end.

Fixpoint trunc_index_inc (n : nat) (k : trunc_index) : trunc_index :=
  match n with
  | O => k
  | S n' => trunc_S (trunc_index_inc n' k)
  end.

Fixpoint is_trunc (n : trunc_index) (A : Type) : Type :=
  match n with
  | minus_two => IsContr A
  | trunc_S n' => forall (x y : A), is_trunc n' (paths x y)
  end.

Parameter Trunc : trunc_index -> Type -> Type.
Parameter tr : forall (n : trunc_index) {A : Type}, A -> Trunc n A.
Parameter is_trunc_Trunc : forall (n : trunc_index) (A : Type), is_trunc n (Trunc n A).
Parameter Trunc_rec : forall (n : trunc_index) {A P : Type}, is_trunc n P -> (A -> P) -> Trunc n A -> P.
Parameter Trunc_rec_beta : forall (n : trunc_index) {A P : Type} (H : is_trunc n P) (f : A -> P) (a : A),
  paths (Trunc_rec n H f (tr n a)) (f a).

(* 3. Connected Types and Connected Maps *)

Definition is_connected (n : trunc_index) (A : Type) : Type :=
  IsContr (Trunc n A).

Definition is_connected_map (n : trunc_index) {A B : Type} (f : A -> B) : Type :=
  forall (y : B), is_connected n (fiber f y).

Axiom contr_is_connected : forall (n : trunc_index) {A : Type},
  IsContr A -> is_connected n A.

Axiom connected_map_monotonic : forall (m n : trunc_index) {A B : Type} (f : A -> B),
  trunc_index_leq m n -> is_connected_map n f -> is_connected_map m f.

(* 4. Loop Spaces and Iterated Loop Spaces *)

Definition LoopSpace (A : Type) (a0 : A) : Type :=
  paths a0 a0.

Definition loop_base (A : Type) (a0 : A) : LoopSpace A a0 :=
  idpath a0.

Fixpoint IteratedLoopSpace (k : nat) : forall (A : Type), A -> Type :=
  fun A a0 =>
    match k with
    | O => A
    | S k' => IteratedLoopSpace k' (LoopSpace A a0) (idpath a0)
    end.

Axiom loop_space_connected : forall (n : trunc_index) {A : Type} (a0 : A),
  is_connected (trunc_S n) A -> is_connected n (LoopSpace A a0).

(* 5. Suspension Higher Inductive Type *)

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

Definition Susp_rec {A Y : Type} (n s : Y) (m : A -> paths n s) : Susp A -> Y :=
  Susp_ind (fun _ => Y) n s (fun a => concat (transport_const (merid A a) n) (m a)).

Axiom Susp_rec_beta_merid : forall {A Y : Type} (n s : Y) (m : A -> paths n s) (a : A),
  paths (ap (Susp_rec n s m) (merid A a)) (m a).

End Suspension.

Axiom suspension_connected : forall (n : trunc_index) {A : Type},
  is_connected n A -> is_connected (trunc_S n) (Susp A).

(* 6. Canonical Freudenthal Suspension Map *)

Definition freudenthal_map {A : Type} (a0 : A) (a : A) : LoopSpace (Susp A) north :=
  concat (merid A a) (inverse (merid A a0)).

Theorem freudenthal_map_base {A : Type} (a0 : A) :
  paths (freudenthal_map a0 a0) (idpath north).
Proof.
  unfold freudenthal_map.
  apply concat_pV.
Defined.

(* 7. Pushouts and Homotopy Pullbacks *)

Module Export Pushout.

Private Inductive Pushout {A B C : Type} (f : C -> A) (g : C -> B) : Type :=
  | push_inl : A -> Pushout f g
  | push_inr : B -> Pushout f g.

Arguments push_inl {A B C f g} _.
Arguments push_inr {A B C f g} _.

Axiom push_glue : forall {A B C : Type} {f : C -> A} {g : C -> B} (c : C),
  paths (@push_inl A B C f g (f c)) (@push_inr A B C f g (g c)).

Definition Pushout_ind {A B C : Type} {f : C -> A} {g : C -> B}
  (P : Pushout f g -> Type)
  (i_l : forall (a : A), P (push_inl a))
  (i_r : forall (b : B), P (push_inr b))
  (gl : forall (c : C), paths (transport P (push_glue c) (i_l (f c))) (i_r (g c)))
  : forall (x : Pushout f g), P x :=
  fun x => match x return P x with
           | push_inl a => i_l a
           | push_inr b => i_r b
           end.

Axiom Pushout_ind_beta_glue : forall {A B C : Type} {f : C -> A} {g : C -> B}
  (P : Pushout f g -> Type)
  (i_l : forall (a : A), P (push_inl a))
  (i_r : forall (b : B), P (push_inr b))
  (gl : forall (c : C), paths (transport P (push_glue c) (i_l (f c))) (i_r (g c)))
  (c : C),
  paths (apd (Pushout_ind P i_l i_r gl) (push_glue c)) (gl c).

Definition Pushout_rec {A B C Y : Type} {f : C -> A} {g : C -> B}
  (i_l : A -> Y) (i_r : B -> Y)
  (gl : forall (c : C), paths (i_l (f c)) (i_r (g c)))
  : Pushout f g -> Y :=
  Pushout_ind (fun _ => Y) i_l i_r
    (fun c => concat (transport_const (push_glue c) (i_l (f c))) (gl c)).

Axiom Pushout_rec_beta_glue : forall {A B C Y : Type} {f : C -> A} {g : C -> B}
  (i_l : A -> Y) (i_r : B -> Y)
  (gl : forall (c : C), paths (i_l (f c)) (i_r (g c)))
  (c : C),
  paths (ap (Pushout_rec i_l i_r gl) (push_glue c)) (gl c).

End Pushout.

Definition HomotopyPullback {A B X : Type} (f : A -> X) (g : B -> X) : Type :=
  { a : A & { b : B & paths (f a) (g b) } }.

Definition blakers_massey_comparison {A B C : Type} {f : C -> A} {g : C -> B} (c : C)
  : HomotopyPullback (@push_inl A B C f g) (@push_inr A B C f g) :=
  existT (fun a => { b : B & paths (@push_inl A B C f g a) (@push_inr A B C f g b) })
         (f c)
         (existT (fun b => paths (@push_inl A B C f g (f c)) (@push_inr A B C f g b))
                 (g c)
                 (push_glue c)).

(* 8. The Blakers-Massey Homotopy Excision Theorem *)

Axiom blakers_massey_theorem : forall {A B C : Type} {f : C -> A} {g : C -> B} (n m : trunc_index),
  is_connected_map n f ->
  is_connected_map m g ->
  is_connected_map (trunc_index_add n m) (blakers_massey_comparison (f:=f) (g:=g)).

(* 9. The Freudenthal Suspension Theorem *)

Axiom freudenthal_suspension_theorem : forall {A : Type} (a0 : A) (n : trunc_index),
  is_connected n A ->
  is_connected_map (trunc_index_add n n) (freudenthal_map a0).

(* 10. Homotopy Groups and Stability Equivalence *)

Definition Pi_k (k : nat) (A : Type) (a0 : A) : Type :=
  Trunc zero_type (IteratedLoopSpace k A a0).

Axiom freudenthal_stability_equiv : forall {A : Type} (a0 : A) (n : trunc_index) (k : nat),
  is_connected n A ->
  trunc_index_leq (trunc_index_inc (S k) minus_two) (trunc_index_add n n) ->
  Equiv (Pi_k k A a0) (Pi_k (S k) (Susp A) north).

