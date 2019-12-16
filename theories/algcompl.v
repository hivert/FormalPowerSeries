(** Truncated polynomial, i.e. polynom mod X^n *)
(******************************************************************************)
(*       Copyright (C) 2019 Florent Hivert <florent.hivert@lri.fr>            *)
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
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple finfun bigop finset fingroup.
From mathcomp Require Import perm ssralg poly polydiv mxpoly binomial bigop.
From mathcomp Require Import finalg zmodp matrix mxalgebra polyXY ring_quotient.
From mathcomp Require Import generic_quotient.

Require Import auxresults.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.
Local Open Scope ring_scope.

Module ComAlgebra.

Section ClassDef.

Variable R : ringType. (* Should this be comRingType ? *)

Record class_of (T : Type) : Type := Class {
  base : Algebra.class_of R T;
  mixin : commutative (Ring.mul base)
}.
Definition base2 R m := ComRing.Class (@mixin R m).
Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun mT m & phant_id (ComRing.mixin (ComRing.class mT)) m =>
  Pack (Phant R) (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @Zmodule.Pack cT xclass.
Definition ringType := @Ring.Pack cT xclass.
Definition comRingType := @ComRing.Pack cT xclass.
Definition lmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @Algebra.Pack R phR cT xclass.
Definition lmod_comRingType := @Lmodule.Pack R phR comRingType xclass.
Definition lalg_comRingType := @Lalgebra.Pack R phR comRingType xclass.
Definition alg_comRingType := @Algebra.Pack R phR comRingType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_comRingType.
Canonical lalg_comRingType.
Canonical alg_comRingType.

Notation comAlgType R := (type (Phant R)).
Notation "[ 'comAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'comAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End ComAlgebra.
Import ComAlgebra.Exports.


Section Tests.

Variable R : comRingType.
Let polyCA := [comAlgType R of {poly R}].

Variable A : comAlgType R.

Example test (c : R) (x y : A) : x * (c *: y) = y * (c *: x).
Proof. by rewrite mulrC -scalerAl scalerAr. Qed.

End Tests.



Module ComUnitAlgebra.

Section ClassDef.

Variable R : ringType. (* Should this be comRingType ? *)

Record class_of (T : Type) : Type := Class {
  base : ComAlgebra.class_of R T;
  mixin : GRing.UnitRing.mixin_of (Ring.Pack base)
}.
Definition base2 R m := UnitAlgebra.Class (@mixin R m).
Local Coercion base : class_of >-> ComAlgebra.class_of.
Local Coercion base2 : class_of >-> UnitAlgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : ComAlgebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.mixin (UnitRing.class mT)) m =>
  Pack (Phant R) (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @Zmodule.Pack cT xclass.
Definition ringType := @Ring.Pack cT xclass.
Definition unitRingType := @UnitRing.Pack cT xclass.
Definition comRingType := @ComRing.Pack cT xclass.
Definition lmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @Algebra.Pack R phR cT xclass.
Definition comAlgType := @ComAlgebra.Pack R phR cT xclass.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass.

Definition comUnitRingType := @ComUnitRing.Pack cT xclass.


End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_comRingType.
Canonical lalg_comRingType.
Canonical alg_comRingType.

Notation comAlgType R := (type (Phant R)).
Notation "[ 'comAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'comAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End ComAlgebra.
Import ComAlgebra.Exports.
























