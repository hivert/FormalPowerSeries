(******************************************************************************)
(*       Copyright (C) 2019-2021 Florent Hivert <florent.hivert@lri.fr>       *)
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
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar.


Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition directed (T : Type) (R : T -> T -> bool) :=
  forall x y : T, { z | R x z & R y z }.

Module Directed.
Section ClassDef.

Record mixin_of (disp : unit)
       (T : porderType disp) := Mixin { _ : directed (@Order.le disp T) }.
Record class_of (T : Type) := Class {
  base  : Order.POrder.class_of T;
  mixin_disp : unit;
  mixin : mixin_of (Order.POrder.Pack mixin_disp base)
}.

Local Coercion base : class_of >-> Order.POrder.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack disp T c.
Definition clone_with disp' c of phant_id class c := @Pack disp' T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack d0 b0 (m0 : mixin_of (@Order.POrder.Pack d0 T b0)) :=
  fun bT b & phant_id (@Order.POrder.class disp bT) b =>
  fun m & phant_id m0 m => Pack disp (@Class T b d0 m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition porderType := @Order.POrder.Pack disp cT xclass.
End ClassDef.

Module Exports.
Coercion base : class_of >-> Order.POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Canonical eqType.
Canonical choiceType.
Canonical porderType.
Notation dirType  := type.
Notation dirMixin := mixin_of.
Notation DirMixin := Mixin.
Notation DirType T m := (@pack T _ _ _ m _ _ id _ id).
Notation "[ 'dirType' 'of' T 'for' cT ]" := (@clone T _ cT _ id)
  (at level 0, format "[ 'dirType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'dirType' 'of' T 'for' cT 'with' disp ]" :=
  (@clone_with T _ cT disp _ id)
  (at level 0, format "[ 'dirType'  'of'  T  'for'  cT  'with'  disp ]") :
  form_scope.
Notation "[ 'dirType' 'of' T ]" := [dirType of T for _]
  (at level 0, format "[ 'dirType'  'of'  T ]") : form_scope.
Notation "[ 'dirType' 'of' T 'with' disp ]" :=
  [dirType of T for _ with disp]
  (at level 0, format "[ 'dirType'  'of'  T  'with' disp ]") : form_scope.
End Exports.

End Directed.
Export Directed.Exports.

Lemma directedP (disp : unit) (T : dirType disp) : directed (T := T) <=%O.
Proof. by case: T => sort [/= bs mx []]. Qed.


Section Generic.
Variables (disp : unit) (T : latticeType disp).

Fact lattice_directed : directed (T := T) <=%O.
Proof. by move=> x y; exists (x `|` y); [apply: leUl |apply: leUr]. Qed.
Definition lattice_dirMixin := DirMixin lattice_directed.
Canonical lattice_dirType := DirType T lattice_dirMixin.

End Generic.

Canonical nat_dirType := DirType nat (@lattice_dirMixin _ _).
Canonical natdvd_dirType := DirType natdvd (@lattice_dirMixin _ _).


Section UpSets.

Variables (disp : unit) (I : dirType disp).
Implicit Types (i j k : I).
Implicit Types (s t : set I).

Definition up_set (S : set I) :=
  nonempty S /\ forall i j, i <= j -> S i -> S j.

Lemma up_setI S T : up_set S -> up_set T -> up_set (S `&` T).
Proof.
move=> [[x Sx upS]] [[y Sy upT]]; split.
- have [z le_xz le_yz] := directedP x y; exists z.
  by split; [apply: upS; first exact: le_xz | apply: upT; first exact: le_yz].
by move=> i j le_ij [/(upS _ _ le_ij) Si /(upT _ _ le_ij) Sj].
Qed.
Lemma up_setU S T : up_set S -> up_set T -> up_set (S `|` T).
Proof.
move=> [[x Sx upS]] [[y Sy upT]]; split; first by exists x; left.
by move=> i j le_ij [/(upS _ _ le_ij) Si | /(upT _ _ le_ij) Sj]; [left|right].
Qed.

Variables (T : Type) (P : set T) (F : T -> set I).

Lemma up_set_bigcup :
  nonempty P ->
  (forall t : T, P t -> up_set (F t)) ->
  up_set (\bigcup_(t in P) F t).
Proof.
move=> [t Pt] H; split.
  by have [[i Fti] _] := H t Pt; exists i; exists t.
move=> {t Pt} i j le_ij [t Pt Fti]; exists t => //.
by have [_ ] := (H t Pt); apply; first apply: le_ij.
Qed.

End UpSets.

