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
From mathcomp Require Import all_ssreflect all_algebra.
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.


Import Order.Def.
Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'invlim' S }"
         (at level 0, format "{ 'invlim'  S }").



Delimit Scope invlim_scope with ILim.

Definition directed (T : Type) (R : T -> T -> bool) :=
  forall x y : T, { z | R x z & R y z }.

Module Directed.
Section ClassDef.

Record mixin_of d (T : porderType d) := Mixin { _ : directed (@le d T) }.

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

Lemma directedP (key : unit) (T : dirType key) : directed (T := T) <=%O.
Proof. by case: T => sort [/= bs mx []]. Qed.


Lemma leq_dir : directed leq.
Proof. by move=> i j; exists (maxn i j); [apply leq_maxl | apply leq_maxr]. Qed.

Definition nat_dirMixin := DirMixin leq_dir.
Canonical nat_dirType := DirType nat nat_dirMixin.


Open Scope order_scope.

Section InverseSystem.

Variables (key : unit) (I : dirType key).

(** Objects and morphisms of the inverse system at left outside the record *)
(** below to allows the addition of more algebraic structure to them.      *)
(** For example : ringType / rmorphism.                                    *)
Variable Ob : I -> Type.
Variable Mor : (forall i j, i <= j -> Ob j -> Ob i).
Record invsys : Type := InvSys {
      invsys_i0 : I;
      invsys_id : forall i (Hii : i <= i), (Mor Hii) =1 id;
      invsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (Mor Hij) \o (Mor Hjk) =1 (Mor (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition invsys_obj (Sys : invsys) := Ob.
Definition invsys_mor (Sys : invsys) := Mor.
Definition ilcomm (Sys : invsys) (fam : forall i, Ob i) :=
  forall i j, forall (Hij : i <= j), Mor Hij (fam j) = fam i.
Definition iscompat (Sys : invsys) (T : Type) (morT : forall i, T -> Ob i) :=
  forall i j, forall (Hij : i <= j), (Mor Hij) \o (morT j) =1 morT i.

Variable Sys : invsys.
Record invlim := InvLim { ilfam :> forall i, Ob i; _ : ilcomm Sys ilfam; }.

Definition invlim_of of phant ((invsys_obj Sys) (invsys_i0 Sys)) := invlim.
Identity Coercion type_invlim_of : invlim_of >-> invlim.

Notation "{ 'invlim' S }" := (invlim_of (Phant ((invsys_obj S) (invsys_i0 S)))).

Canonical invlim_eqType := EqType invlim gen_eqMixin.
Canonical invlimp_eqType := EqType {invlim Sys} gen_eqMixin.
Canonical invlim_choiceType := ChoiceType invlim gen_choiceMixin.
Canonical invlimp_choiceType := ChoiceType {invlim Sys} gen_choiceMixin.

End InverseSystem.
Notation "{ 'invlim' S }" := (invlim_of (Phant ((invsys_obj S) (invsys_i0 S)))).


Section InverseLimitTheory.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> Type.
Variable Mor : (forall i j, i <= j -> Ob j -> Ob i).

Variable Sys : invsys Mor.
Implicit Type x y : {invlim Sys}.

Definition ilproj i : {invlim Sys} -> Ob i := (ilfam (Sys := Sys))^~ i.

Lemma ilprojE x :
  forall i j, forall (Hij : i <= j), Mor Hij (ilproj j x) = (ilproj i x).
Proof. by case: x. Qed.

Lemma ilprojP : iscompat Sys ilproj.
Proof. by move=> i j Hij [fam Hfam] /=; apply Hfam. Qed.

Lemma invlimP x y : (forall i, ilproj i x = ilproj i y) -> x = y.
Proof.
case: x y => [fx Hx] [fy Hy] /= H.
have {H} H : fx = fy by apply functional_extensionality_dep.
by subst fy; have -> : Hx = Hy by apply Prop_irrelevance.
Qed.


Section UniversalProperty.

Variable (T : Type) (f : forall i, T -> Ob i).
Hypothesis Hcomp : iscompat Sys f.

Lemma iluniv_spec :
  {iluniv : T -> invlim Sys | forall i, (ilproj i) \o iluniv = f i}.
Proof.
move: Hcomp; rewrite /iscompat => Hf; pose fil t i := f i t.
have Hfil t : ilcomm Sys (fil t) by rewrite /fil=> i j Hij; apply Hf.
by exists (fun t => InvLim (Hfil t)).
Qed.
Definition iluniv := let: exist f _ := iluniv_spec in f.
Lemma ilunivP i t : ilproj i (iluniv t) = f i t.
Proof.
rewrite /iluniv; move: t; case: iluniv_spec => un Hun t.
by rewrite -Hun.
Qed.

Lemma ilunivE (un : T -> invlim Sys) :
  (forall i, (ilproj i) \o un =1 f i) -> un =1 iluniv.
Proof.
move=> H x; apply invlimP=> i.
by rewrite -/((ilproj i \o un) _) H ilunivP.
Qed.

End UniversalProperty.

End InverseLimitTheory.


Open Scope ring_scope.
Import GRing.Theory.

Section InvLimitZModType.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> zmodType.
Variable Mor : forall i j, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type x y : {invlim Sys}.

Fact ilzeroP : ilcomm Sys (fun i => 0 : Ob i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : {invlim Sys} := InvLim ilzeroP.

Fact iloppP x : ilcomm Sys (fun i => - (ilproj i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : {invlim Sys} := InvLim (iloppP x).

Fact iladdP x y : ilcomm Sys (fun i => ilproj i x + ilproj i y).
Proof. by move=> i j Hij; rewrite raddfD (ilprojE x) (ilprojE y). Qed.
Definition iladd x y : {invlim Sys} := InvLim (iladdP x y).

Program Definition invlim_zmodMixin :=
  @ZmodMixin {invlim Sys} ilzero ilopp iladd _ _ _ _.
Next Obligation. by move=> a b c; apply invlimP=> i; rewrite /= addrA. Qed.
Next Obligation. by move=> a b; apply invlimP=> i; rewrite /= addrC. Qed.
Next Obligation. by move=> b; apply invlimP=> i; rewrite /= add0r. Qed.
Next Obligation. by move=> b; apply invlimP=> i; rewrite /= addNr. Qed.
Canonical invlim_zmodType :=
  Eval hnf in ZmodType (invlim Sys) invlim_zmodMixin.
Canonical invlimp_zmodType :=
  Eval hnf in ZmodType {invlim Sys} invlim_zmodMixin.

Fact ilproj_is_additive i : additive (ilproj (Sys := Sys) i).
Proof. by []. Qed.
Canonical ilproj_additive i := Additive (ilproj_is_additive i).

Lemma il_neq0 x : x != 0 -> exists i, ilproj i x != 0.
Proof.
move=> Hx; apply/existsbP; move: Hx; apply contraR => /=.
rewrite existsbE => /forallp_asboolPn Hall.
apply/eqP/invlimP=> i; rewrite -/(ilproj i x) -/(ilproj i 0) raddf0.
by have /negP := Hall i; rewrite negbK => /eqP.
Qed.


Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact iluniv_is_additive : additive (iluniv Hcomp).
Proof.
by move=> t u; apply invlimP=> i; rewrite ilunivP !raddfB /= !ilunivP.
Qed.
Canonical iluniv_additive := Additive iluniv_is_additive.

End UniversalProperty.

End InvLimitZModType.



Section InvLimitRing.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> ringType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}).

Fact iloneP : ilcomm Sys (fun i => 1 : Ob i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : {invlim Sys} := InvLim iloneP.

Fact ilmulP x y : ilcomm Sys (fun i => ilproj i x * ilproj i y).
Proof. by move=> i j Hij; rewrite rmorphM (ilprojE x) (ilprojE y). Qed.
Definition ilmul x y : {invlim Sys} := InvLim (ilmulP x y).

Program Definition invlim_ringMixin :=
  @RingMixin [zmodType of {invlim Sys}] ilone ilmul _ _ _ _ _ _.
Next Obligation. by move=> a b c; apply invlimP=> i; rewrite /= mulrA. Qed.
Next Obligation. by move=> a; apply invlimP=> i; rewrite /= mul1r. Qed.
Next Obligation. by move=> a; apply invlimP=> i; rewrite /= mulr1. Qed.
Next Obligation. by move=> a b c; apply invlimP=> i /=; rewrite /= mulrDl. Qed.
Next Obligation. by move=> a b c; apply invlimP=> i /=; rewrite /= mulrDr. Qed.
Next Obligation.
apply/negP => /eqP/(congr1 (fun x => x (invsys_i0 Sys))) /= /eqP.
exact/negP/oner_neq0.
Qed.
Canonical invlim_ringType :=
  Eval hnf in RingType (invlim Sys) invlim_ringMixin.
Canonical invlimp_ringType :=
  Eval hnf in RingType {invlim Sys} invlim_ringMixin.

Fact ilproj_is_multiplicative i : multiplicative (ilproj (Sys := Sys) i).
Proof. by []. Qed.
Canonical ilproj_multiplicative i := AddRMorphism (ilproj_is_multiplicative i).


Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact iluniv_is_multiplicative : multiplicative (iluniv Hcomp).
Proof.
split.
- by move=> t u; apply invlimP=> i; rewrite ilunivP rmorphM /= !ilunivP.
- by apply invlimP=> i; rewrite ilunivP !rmorph1.
Qed.
Canonical iluniv_multiplicative := AddRMorphism iluniv_is_multiplicative.

End UniversalProperty.

End InvLimitRing.


Section InvLimitComRing.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> comRingType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}).

Fact ilmulC x y : x * y = y * x.
Proof. by apply invlimP=> i; rewrite /= mulrC. Qed.
Canonical invlim_comRingType :=
  Eval hnf in ComRingType (invlim Sys) ilmulC.
Canonical invlimp_comRingType :=
  Eval hnf in ComRingType {invlim Sys} ilmulC.

End InvLimitComRing.


Section InvLimitUnitRing.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> unitRingType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}).

Definition ilunit x := `[forall i, ilproj i x \is a GRing.unit].

Fact inv_isunitP x :
  (forall i, ilproj i x \is a GRing.unit) ->
  ilcomm Sys (fun i => (ilproj i x)^-1).
Proof.
by move=> Hunit i j ilej; rewrite /= rmorphV ?(ilprojE x) // Hunit.
Qed.
Definition ilinv x : {invlim Sys} :=
  if pselect (forall i, ilproj i x \is a GRing.unit) is left Pf
  then InvLim (inv_isunitP Pf) else x.

Fact ilmulVr : {in ilunit, left_inverse 1 ilinv *%R}.
Proof.
move=> x /forallbP Hinv; apply invlimP=> i.
rewrite /ilinv; case: pselect => /= [_|/(_ Hinv)//].
by rewrite mulVr // Hinv.
Qed.
Fact ilmulrV : {in ilunit, right_inverse 1 ilinv *%R}.
Proof.
move=> x /forallbP Hinv; apply invlimP=> i.
rewrite /ilinv; case: pselect => /= [_|/(_ Hinv)//].
by rewrite mulrV // Hinv.
Qed.
Fact ilunitP x y : y * x = 1 /\ x * y = 1 -> ilunit x.
Proof.
move=> [Hxy Hyx]; apply/forallbP => i; apply/unitrP.
by exists (ilproj i y); rewrite -!rmorphM Hxy Hyx.
Qed.
Fact ilinv0id : {in [predC ilunit], ilinv =1 id}.
Proof.
move=> x; rewrite inE /= => /forallbP Hx.
by rewrite /ilinv; case: pselect => /= [/= H|//]; have:= Hx H.
Qed.
Canonical invlim_unitRingMixin :=
  Eval hnf in UnitRingMixin ilmulVr ilmulrV ilunitP ilinv0id.
Canonical invlim_unitRingType :=
  Eval hnf in UnitRingType (invlim Sys) invlim_unitRingMixin.
Canonical invlimp_unitRingType :=
  Eval hnf in UnitRingType {invlim Sys} invlim_unitRingMixin.

End InvLimitUnitRing.


Section InvLimitComUnitRing.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> comUnitRingType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Canonical invlim_comUnitRingType :=
  Eval hnf in [comUnitRingType of invlim Sys].
Canonical invlimp_comUnitRingType :=
  Eval hnf in [comUnitRingType of {invlim Sys}].

End InvLimitComUnitRing.



Section InvLimitIDomain.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> idomainType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}).

Fact ilmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> H; case: (altP (x =P 0)) => //= /il_neq0 [i Hi].
move: H; apply contra_eqT => /il_neq0 [j Hj].
have [k ilek jlek] := directedP i j.
have {Hi} /negbTE Hx : ilproj k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (Mor ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
have {Hj} /negbTE Hy : ilproj k y != 0.
  move: Hj; apply contra => /eqP/(congr1 (Mor jlek)).
  by rewrite (ilprojE y) raddf0 => ->.
apply/negP => /eqP/(congr1 (ilproj k))/eqP.
by rewrite rmorph0 rmorphM mulf_eq0 Hx Hy.
Qed.

Canonical invlim_idomainType :=
  Eval hnf in IdomainType (invlim Sys) ilmul_eq0.
Canonical invlimp_idomainType :=
  Eval hnf in IdomainType {invlim Sys} ilmul_eq0.

End InvLimitIDomain.



Section InvLimitLinear.

Variables (key : unit) (I : dirType key).
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable Mor : forall i j, (i <= j)%O -> {linear (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}) (r : R).

Fact ilscaleP r x : ilcomm Sys (fun i => r *: ilproj i x).
Proof. by move=> i j Hij; rewrite linearZ (ilprojE x). Qed.
Definition ilscale r x : {invlim Sys} := InvLim (ilscaleP r x).

Program Definition invlim_lmodMixin :=
  @LmodMixin R [zmodType of {invlim Sys}] ilscale _ _ _ _.
Next Obligation. by apply invlimP=> i /=; rewrite scalerA. Qed.
Next Obligation. by move=> x; apply invlimP=> i /=; rewrite scale1r. Qed.
Next Obligation. by move=> r x y; apply invlimP=> i /=; rewrite scalerDr. Qed.
Next Obligation. by move=> r s; apply invlimP=> i /=; rewrite scalerDl. Qed.

Canonical invlim_lmodType :=
  Eval hnf in LmodType R (invlim Sys) invlim_lmodMixin.
Canonical invlimp_lmodType :=
  Eval hnf in LmodType R {invlim Sys} invlim_lmodMixin.

Fact ilproj_is_linear i : linear (ilproj (Sys := Sys) i).
Proof. by []. Qed.
Canonical ilproj_linear i := AddLinear (ilproj_is_linear i).


Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact iluniv_is_linear : linear (iluniv Hcomp).
Proof.
by move=> r t u; apply invlimP=> i; rewrite !ilunivP !linearP /= !ilunivP.
Qed.
Canonical iluniv_linear := AddLinear iluniv_is_linear.

End UniversalProperty.

End InvLimitLinear.



Section InvLimitLalg.

Variables (key : unit) (I : dirType key).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable Mor : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}) (r : R).


Fact ilscaleAl r x y : ilscale r (x * y) = ilscale r x * y.
Proof. by apply invlimP=> i /=; rewrite scalerAl. Qed.
Canonical invlim_lalgType :=
  Eval hnf in LalgType R (invlim Sys) ilscaleAl.
Canonical invlimp_lalgType :=
  Eval hnf in LalgType R {invlim Sys} ilscaleAl.

Canonical ilproj_lrmorphism i := AddLRMorphism (ilproj_is_linear i).

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.
Canonical iluniv_lrmorphism := AddLRMorphism (iluniv_is_linear Hcomp).

End UniversalProperty.

End InvLimitLalg.



Section InvLimitAlg.

Variables (key : unit) (I : dirType key).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable Mor : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Implicit Type (x y : {invlim Sys}) (r : R).


Fact ilscaleAr r x y : ilscale r (x * y) = x * ilscale r y.
Proof. by apply invlimP=> i /=; rewrite scalerAr. Qed.
Canonical invlim_algType :=
  Eval hnf in AlgType R (invlim Sys) ilscaleAr.
Canonical invlimp_algType :=
  Eval hnf in AlgType R {invlim Sys} ilscaleAr.

End InvLimitAlg.


Section InvLimitUnitAlg.

Variables (key : unit) (I : dirType key).
Variables (R : comUnitRingType).
Variable Ob : I -> unitAlgType R.
Variable Mor : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Canonical invlim_unitalgType := [unitAlgType R of (invlim Sys)].
Canonical invlimp_unitalgType := [unitAlgType R of {invlim Sys}].

End InvLimitUnitAlg.



Section InvLimitField.

Variables (key : unit) (I : dirType key).
Variable Ob : I -> fieldType.
Variable Mor : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys Mor.

Fact invlim_fieldMixin : GRing.Field.mixin_of [unitRingType of {invlim Sys}].
Proof.
move=> x /il_neq0 [i Hi].
rewrite unfold_in /= /ilunit; apply/forallbP => j; rewrite unitfE.
have [k ilek jlek] := directedP i j.
have {Hi} : ilproj k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (Mor ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
by rewrite -(ilprojE x jlek) fmorph_eq0.
Qed.
Canonical invlim_fieldType :=
  Eval hnf in FieldType (invlim Sys) invlim_fieldMixin.
Canonical invlimp_fieldType :=
  Eval hnf in FieldType {invlim Sys} invlim_fieldMixin.

End InvLimitField.



Section CNVars.

Import GRing.Theory.
Open Scope ring_scope.
Variable R : comRingType.

Section Defs.

Variable (m n : nat).
Hypothesis (nlem : (n <= m)%N).

Fact cnvar_tupleP :
  @size {mpoly R[n]}
        (take m [tuple 'X_i | i < n] ++ [tuple 0 | i < m - n]) == m.
Proof. by rewrite size_cat !size_tuple /minn ltnNge nlem /= subnKC. Qed.
Definition cnvar_tuple := Tuple cnvar_tupleP.
Definition cnvar p := p \mPo cnvar_tuple.

Lemma cnvar_is_rmorphism : rmorphism cnvar.
Proof. repeat split; [exact: rmorphB | exact: rmorphM | exact: rmorph1]. Qed.
Canonical cnvar_additive := Additive cnvar_is_rmorphism.
Canonical cnvar_rmorphism := RMorphism cnvar_is_rmorphism.

Lemma cnvar_is_linear : linear cnvar.
Proof. by rewrite /cnvar; exact: linearP. Qed.
Canonical cnvar_linear := AddLinear cnvar_is_linear.
Canonical cnvar_lrmorphism := [lrmorphism of cnvar].


Lemma tnth_cnvar_tuple (i : 'I_m) (ilen : (i < n)%N) :
  tnth cnvar_tuple i = 'X_(Ordinal ilen).
Proof.
rewrite (tnth_nth 0) /= nth_cat size_take size_map size_enum_ord.
rewrite (ltnNge m n) nlem /= ilen.
rewrite nth_take ?(leq_trans ilen) //.
rewrite (nth_map (Ordinal ilen)) ?size_enum_ord //; congr ('X_ _).
by apply val_inj; rewrite /= nth_enum_ord.
Qed.

Lemma tnth_cnvar_tuple0 (i : 'I_m) : (n <= i)%N -> tnth cnvar_tuple i = 0.
Proof.
move=> nlei; rewrite (tnth_nth 0) /= nth_cat size_take size_map size_enum_ord.
rewrite (ltnNge m n) nlem /= (ltnNge i n) nlei /=.
have nltm : (0 < m - n)%N by rewrite subn_gt0 (leq_ltn_trans nlei).
apply: (nth_map (Ordinal nltm)).
by rewrite size_enum_ord -(ltn_add2r n) !subnK.
Qed.

End Defs.

Lemma cnvarE n m (H1 H2 : (n <= m)%N) : cnvar H1 =1 cnvar H2.
Proof. by move=> p; rewrite /cnvar; congr (_ \mPo _); apply: val_inj. Qed.

Lemma cnvar_id n (H : (n <= n)%N) : cnvar H =1 id.
Proof.
move=> p; rewrite /cnvar.
suff -> : cnvar_tuple H = [tuple 'X_i | i < n] by rewrite comp_mpoly_id.
apply eq_from_tnth => i.
rewrite tnth_cnvar_tuple /= tnth_mktuple; congr ('X_ _).
exact: val_inj.
Qed.

Lemma cnvar_compat i j k  (Hij : (i <= j)%N) (Hjk : (j <= k)%N) :
  (cnvar Hij) \o (cnvar Hjk) =1 (cnvar (leq_trans Hij Hjk)).
Proof.
move=> p /=; rewrite /cnvar !(comp_mpolyE p).
rewrite raddf_sum /=; apply eq_bigr => m _.
rewrite comp_mpolyZ; congr (_ *: _).
rewrite rmorph_prod /=; apply eq_bigr => l _.
rewrite !rmorphX /=; congr (_ ^+ _).
case: (ltnP l i) => [llti | ilel].
- rewrite !tnth_cnvar_tuple ?(leq_trans llti Hij) // => Hlj.
  by rewrite comp_mpolyXU -tnth_nth !tnth_cnvar_tuple.
- rewrite [RHS]tnth_cnvar_tuple0 //.
  case: (ltnP l j) => [lltj|jlel].
  + by rewrite tnth_cnvar_tuple comp_mpolyXU -tnth_nth tnth_cnvar_tuple0.
  + by rewrite tnth_cnvar_tuple0 // comp_mpoly0.
Qed.

Local Lemma leEnat_impl i j : (i <= j)%O -> (i <= j)%N.
Proof. by rewrite leEnat. Qed.

Lemma cnvar_idO n (H : (n <= n)%O) : cnvar (leEnat_impl H) =1 id.
Proof. exact: cnvar_id. Qed.

Lemma cnvar_compatO i j k  (Hij : (i <= j)%O) (Hjk : (j <= k)%O) :
  (cnvar (leEnat_impl Hij)) \o (cnvar (leEnat_impl Hjk))
  =1 (cnvar (leEnat_impl (le_trans Hij Hjk))).
Proof. by move=> p; rewrite cnvar_compat; apply cnvarE. Qed.

Definition mpoly_invsys := InvSys 0%N cnvar_idO cnvar_compatO.

End CNVars.


Let lm (R : comRingType) := [lmodType R of {invlim mpoly_invsys R}].
Let zm (R : comRingType) := [zmodType of {invlim mpoly_invsys R}].
Let za (R : comRingType) := [algType R of {invlim mpoly_invsys R}].

Lemma test (R : comRingType) (r : R) (x y : {invlim mpoly_invsys R}) :
  ilproj 2 (r *: (x * y)) = ilproj 2 y * ilproj 2 (r *: x).
Proof. by rewrite linearZ /= mulrC scalerAr. Qed.
