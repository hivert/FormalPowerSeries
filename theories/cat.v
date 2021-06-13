(******************************************************************************)
(*       Copyright (C) 2021 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From mathcomp Require Import all_ssreflect ssralg vector.
From mathcomp Require Import boolp classical_sets.


Reserved Notation "\pi_1" (at level 8, format "\pi_1").
Reserved Notation "\pi_2" (at level 8, format "\pi_2").
Reserved Notation "\ind" (at level 8, format "\ind").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.


(***************************************************************************)
(** Small concrete categories                                              *)
(*                                                                         *)
(* All objects are sets modelled in Coq by a choiceType.                   *)
(*                                                                         *)
(***************************************************************************)
Section Def.

Record category := Category {
  TObj : Type;
  TMor : forall A B : TObj, Type;

  objType : TObj -> choiceType;
  morFun : forall A B : TObj, TMor A B -> (objType A) -> (objType B);
  _ : forall A B (f g : TMor A B), (morFun f =1 morFun g) -> f = g;

  morId : forall A : TObj, TMor A A;
  _ : forall A, morFun (morId A) =1 id;

  morComp : forall A B C : TObj, TMor B C -> TMor A B -> TMor A C;
  _ : forall (A B C : TObj) (f : TMor A B) (g : TMor B C),
    morFun (morComp g f) =1 morFun g \o morFun f;
}.

End Def.

Module Theory.
Section Theory.

Variable Cat : category.

Lemma morext_int (A B : TObj Cat) (f g : TMor A B) :
  morFun f =1 morFun g -> f = g.
Proof. by case: Cat A B f g. Qed.
Lemma moridE_int (A : TObj Cat) : morFun (morId A) =1 id.
Proof. by case: Cat A. Qed.
Lemma morcompE_int (A B C : TObj Cat) (f : TMor A B) (g : TMor B C) :
  morFun (morComp g f) =1 morFun g \o morFun f.
Proof. by case: Cat A B C f g. Qed.

End Theory.

Module Exports.
Section Exports.

Variable Cat : category.

(* Trick to have uniform inheritance *)
Definition Obj := @TObj Cat.
Coercion TObj : category >-> Sortclass.
Definition type_of_Obj := @objType Cat : Obj -> Type.
Coercion type_of_Obj : Obj >-> Sortclass.

Definition Mor := @TMor Cat.
Definition fun_of_Mor (A B : Obj) := @morFun Cat A B : Mor A B -> A -> B.
Coercion fun_of_Mor : Mor >-> Funclass.

Definition morid A : Mor A A := morId A.
Definition morcomp A B C f g : Mor A C := @morComp Cat A B C f g.

Local Infix "\O" := morcomp (at level 30).

Lemma morext A B (f g : Mor A B) : f =1 g -> f = g.
Proof. exact: morext_int. Qed.
Lemma moridE (A : Obj) : morid A =1 id.
Proof. exact: moridE_int. Qed.
Lemma morcompE (A B C : Obj) (f : Mor A B) (g : Mor B C) :
    g \O f =1 g \o f.
Proof. exact: morcompE_int. Qed.

End Exports.
End Exports.
End Theory.
Export Theory.Exports.

Notation "\id_ A" := (morid A) (at level 0).
Infix "\O" := morcomp (at level 30).


(***************************************************************************)
(** Category Axioms                                                        *)
(*                                                                         *)
(***************************************************************************)
Section CatAxioms.

Variable  Cat : category.
Variables (A B C D : Cat).
Variables (f : Mor A B) (g : Mor B C) (h : Mor C D).

Lemma comp1M : \id_B \O f = f.
Proof. by apply: morext => x; rewrite morcompE /= moridE. Qed.

Lemma compM1 : f \O \id_A = f.
Proof. by apply: morext => x; rewrite morcompE /= moridE. Qed.

Lemma mcompA : (h \O g) \O f = h \O (g \O f).
Proof. by apply: morext => x; rewrite !morcompE /= !morcompE. Qed.

End CatAxioms.


(***************************************************************************)
(** Various Instances : SetCat, ZModCat, RingCat, ...                      *)
(*                                                                         *)
(***************************************************************************)
Notation CatGen rt mt mi mc :=
  (@Category rt mt (fun x => x) (fun A B f => f) _ mi _ mc _).
Notation RingCatGen rt :=
  (@CatGen rt
           (fun A B => {rmorphism A -> B})
           (fun A => [rmorphism of idfun])
           (fun A B C f g => [rmorphism of f \o g])).
Ltac mor_ext f g H := (
  case: f g H => [f f_add] [g g_add] /= /funext Heq;
  subst g; have -> : f_add = g_add by apply: Prop_irrelevance).


Program Definition SetCat : category :=
  @CatGen choiceType (fun A B => A -> B) (fun A => id) (fun A B C f g => f \o g).
Next Obligation. exact: funext. Qed.

Program Definition ZModCat : category :=
  @CatGen zmodType
          (fun A B => {additive A -> B})
          (fun A => [additive of idfun])
          (fun A B C f g => [additive of f \o g]).
Next Obligation. by mor_ext f g H. Qed.
Program Definition RingCat : category := @RingCatGen ringType.
Next Obligation. by mor_ext f g H. Qed.
Program Definition ComRingCat : category := @RingCatGen comRingType.
Next Obligation. by mor_ext f g H. Qed.
Program Definition UnitRingCat : category := @RingCatGen unitRingType.
Next Obligation. by mor_ext f g H. Qed.
Program Definition ComUnitRingCat : category := RingCatGen comUnitRingType.
Next Obligation. by mor_ext f g H. Qed.
Program Definition IDomainCat : category := RingCatGen idomainType.
Next Obligation. by mor_ext f g H. Qed.
Program Definition FieldCat : category := RingCatGen fieldType.
Next Obligation. by mor_ext f g H. Qed.

Program Definition LModCat (R : ringType) : category :=
  @CatGen (lmodType R)
          (fun A B => {linear A -> B})
          (fun A => [linear of idfun])
          (fun A B C f g => [linear of f \o g]).
Next Obligation. by mor_ext f g H. Qed.
Program Definition LAlgCat (R : ringType) : category :=
  CatGen (lalgType R)
         (fun A B => {lrmorphism A -> B})
         (fun A => [lrmorphism of idfun])
         (fun A B C f g => [lrmorphism of f \o g]).
Next Obligation. by mor_ext f g H. Qed.
Program Definition AlgCat (R : ringType) : category :=
  CatGen (algType R)
         (fun A B => {lrmorphism A -> B})
         (fun A => [lrmorphism of idfun])
         (fun A B C f g => [lrmorphism of f \o g]).
Next Obligation. by mor_ext f g H. Qed.

Program Definition VectCat (R : fieldType) :=
  CatGen (vectType R)
         (fun A B => 'Hom(A, B))
         (fun A => @id_lfun _ _)
         (fun A B C f g => (f \o g)%VF).
Next Obligation. exact/lfunP. Qed.
Next Obligation. by move=> x; rewrite id_lfunE. Qed.
Next Obligation. by move=> x; rewrite lfunE. Qed.



(***************************************************************************)
(** Cartesian product functorial construction                              *)
(*                                                                         *)
(***************************************************************************)
Module Product.

Section ClassDefs.
Variables (Cat : category) (X1 X2 : Cat).

Record mixin_of (T : Type) := Mixin {
  TProd : Cat;
  _ : type_of_Obj TProd = T :> Type;
  pi1 : Mor TProd X1;
  pi2 : Mor TProd X2;
  ind : forall (Y : Cat) (f1 : Mor Y X1) (f2 : Mor Y X2), (Mor Y TProd);
  _ : forall (Y : Cat) (f1 : Mor Y X1) (f2 : Mor Y X2),
      pi1 \O ind f1 f2 = f1 /\ pi2 \O ind f1 f2 = f2;
  _ : forall (Y : Cat) (f1 : Mor Y X1) (f2 : Mor Y X2) (indY : Mor Y TProd),
      pi1 \O indY = f1 -> pi2 \O indY = f2 -> indY = ind f1 f2;
}.

Record class_of T := Class {base : Choice.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Choice.class_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition Prod : TObj Cat := TProd (mixin class).

End ClassDefs.

Module Exports.

Coercion Prod : type >-> TObj.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation prodType := type.
Notation ProdMixin := Mixin.

Section Exports.

Variables (Cat : category) (X1 X2 : Cat).
Variable (P : prodType X1 X2).

Definition pi1_phant of phant P : Mor P X1 := pi1 (mixin (class P)).
Definition pi2_phant of phant P : Mor P X2 := pi2 (mixin (class P)).
Local Notation "\pi_1" := (pi1_phant (Phant P)).
Local Notation "\pi_2" := (pi2_phant (Phant P)).
Definition ind_phant of phant P := ind (mixin (class P)).
Local Notation "\ind" := (ind_phant (Phant P)).


Lemma pi_prodE Y (f1 : Mor Y X1) (f2 : Mor Y X2) :
  \pi_1 \O (\ind f1 f2) = f1 /\ \pi_2 \O (\ind f1 f2) = f2.
Proof.
move: Y f1 f2; rewrite /ind_phant /pi1_phant /pi2_phant /Mor /=.
by case: Cat X1 X2 P => TC TM cc cm mE mid midE c CE XX1 XX2 [TP [chP []]].
Qed.

Lemma pi1_prodE Y (f1 : Mor Y X1) (f2 : Mor Y X2) : \pi_1 \O (\ind f1 f2) = f1.
Proof. by have [] := pi_prodE f1 f2. Qed.
Lemma pi2_prodE Y (f1 : Mor Y X1) (f2 : Mor Y X2) : \pi_2 \O (\ind f1 f2) = f2.
Proof. by have [] := pi_prodE f1 f2. Qed.

Lemma prodE Y (f1 : Mor Y X1) (f2 : Mor Y X2) (indY : Mor Y P) :
  \pi_1 \O indY = f1 -> \pi_2 \O indY = f2 -> indY = \ind f1 f2.
Proof.
move: Y f1 f2 indY; rewrite /ind_phant /pi1_phant /pi2_phant /Mor /=.
by case: Cat X1 X2 P => TC TM cc cm mE mid midE c CE XX1 XX2 [TP [chP []]].
Qed.

End Exports.
End Exports.
End Product.
Export Product.Exports.

Notation "\pi_1" := (pi1_phant (Phant _)).
Notation "\pi[ T ]_1'" := (pi1_phant (Phant T)) (at level 8, only parsing).
Notation "\pi_2" := (pi2_phant (Phant _)).
Notation "\pi[ T ]_2'" := (pi2_phant (Phant T)) (at level 8, only parsing).
Notation "\ind" := (ind_phant (Phant _)).
Notation "\ind[ T ]" := (ind_phant (Phant T)) (at level 8, only parsing).

(* Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m). *)

Notation ProdType T m := (@Product.pack _ _ _ T m _ _ id).


Section DefProduct.

Variable (A1 A2 : SetCat).

Program Definition prod_Mixin : Product.mixin_of A1 A2 (A1 * A2)%type :=
  @ProdMixin SetCat A1 A2 (A1 * A2)%type [choiceType of (A1 * A2)%type] _
             (fun p => p.1) (fun p => p.2)
             (fun (Y : choiceType) (f1 : Y -> A1) (f2 : Y -> A2) y => (f1 y, f2 y))
             _ _.
Next Obligation. by apply: funext => y /=; apply: surjective_pairing. Qed.

Canonical prod_ProdType := ProdType (A1 * A2)%type prod_Mixin.

End DefProduct.
