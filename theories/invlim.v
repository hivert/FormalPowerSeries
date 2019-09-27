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
Reserved Notation "''pi_' i" (at level 8, i at level 2, format "''pi_' i").

Delimit Scope invlim_scope with InvLim.


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


Open Scope order_scope.


(***************************************************************************)
(** Inverse systems and inverse limits                                     *)
(*                                                                         *)
(***************************************************************************)
Section InverseLimit.

Variables (disp : unit) (I : dirType disp).

(** Objects and bonding morphisms of the inverse system at left outside    *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Ob : I -> Type.
Variable bonding : (forall i j, i <= j -> Ob j -> Ob i).
Record invsys : Type := InvSys {
      invsys_inh : I;
      invsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      invsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hij) \o (bonding Hjk) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition invsys_obj of invsys := Ob.
Definition invsys_mor of invsys := bonding.
Definition isthread of invsys := fun fam : forall i, Ob i =>
  forall i j, forall (Hij : i <= j), bonding Hij (fam j) = fam i.
Definition iscompat of invsys := fun T (mors : forall i, T -> Ob i) =>
  forall i j, forall (Hij : i <= j), bonding Hij \o mors j =1 mors i.

Variable Sys : invsys.
Record invlim := InvLim { ilfam :> forall i, Ob i; _ : isthread Sys ilfam; }.

Definition invlim_of of phantom invsys Sys := invlim.
Identity Coercion type_invlim_of : invlim_of >-> invlim.

Local Notation "{ 'invlim' S }" := (invlim_of (Phantom _ S)).

Canonical invlim_eqType := EqType invlim gen_eqMixin.
Canonical invlimp_eqType := EqType {invlim Sys} gen_eqMixin.
Canonical invlim_choiceType := ChoiceType invlim gen_choiceMixin.
Canonical invlimp_choiceType := ChoiceType {invlim Sys} gen_choiceMixin.

End InverseLimit.
Notation "{ 'invlim' S }" := (invlim_of (Phantom _ S)).


Section InverseLimitTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.

Variable Sys : invsys bonding.
Implicit Type x y : {invlim Sys}.

Definition ilproj i : {invlim Sys} -> Ob i := (ilfam (Sys := Sys))^~ i.

Lemma ilprojE x :
  forall i j, forall (Hij : i <= j), bonding Hij (ilproj j x) = ilproj i x.
Proof. by case: x. Qed.

Lemma ilprojP : iscompat Sys ilproj.
Proof. by move=> i j Hij [fam Hfam] /=; apply Hfam. Qed.

Local Open Scope invlim_scope.
Notation "''pi_' i" := (ilproj i) : invlim_scope.

Lemma invlimP x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
case: x y => [fx Hx] [fy Hy] /= H.
have {H} H : fx = fy by apply functional_extensionality_dep.
by subst fy; have -> : Hx = Hy by apply Prop_irrelevance.
Qed.

(** Building the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, T -> Ob i).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_spec :
  { ilind : T -> invlim Sys | forall i, 'pi_i \o ilind = f i }.
Proof.
move: Hcomp; rewrite /iscompat => Hf; pose fil t i := f i t.
have Hfil t : isthread Sys (fil t) by rewrite /fil=> i j Hij; apply Hf.
by exists (fun t => InvLim (Hfil t)).
Qed.
Definition ilind := let: exist f _ := ilind_spec in f.
Lemma ilindP i t : 'pi_i (ilind t) = f i t.
Proof.
rewrite /ilind; move: t; case: ilind_spec => un Hun t.
by rewrite -Hun.
Qed.

Lemma ilindE (un : T -> invlim Sys) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 ilind.
Proof.
move=> H x; apply invlimP=> i.
by rewrite -/(('pi_i \o un) _) H ilindP.
Qed.

End UniversalProperty.

End InverseLimitTheory.
Local Open Scope invlim_scope.
Notation "'pi_ i" := (ilproj i) : invlim_scope.


Section InvLimitEqType.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.

Variable Sys : invsys bonding.
Implicit Type x y : {invlim Sys}.

Lemma invlimPn x y : reflect (exists i, 'pi_i x != 'pi_i y) (x != y).
Proof.
apply (iffP idP) => [neq|[i]]; last by apply/contra => /eqP ->.
apply/asboolP; rewrite asbool_existsNb; apply/contra: neq => /asboolP Hx.
by apply/eqP/invlimP => /= i; apply/eqP.
Qed.

End InvLimitEqType.


Open Scope ring_scope.
Import GRing.Theory.

(****************************************************************************)
(** Inverse limits in various algebraic categories                          *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)
Section InvLimitZModType.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type x y : {invlim Sys}.

Fact ilzeroP : isthread Sys (fun i => 0 : Ob i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : {invlim Sys} := InvLim ilzeroP.

Fact iloppP x : isthread Sys (fun i => - ('pi_i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : {invlim Sys} := InvLim (iloppP x).

Fact iladdP x y : isthread Sys (fun i => 'pi_i x + 'pi_i y).
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

Lemma il_neq0 x : x != 0 -> exists i, 'pi_i x != 0.
Proof. by move/invlimPn=> [i]; rewrite raddf0 => Hi; exists i. Qed.

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_is_additive : additive (ilind Hcomp).
Proof.
by move=> t u; apply invlimP=> i; rewrite ilindP !raddfB /= !ilindP.
Qed.
Canonical ilind_additive := Additive ilind_is_additive.

End UniversalProperty.

End InvLimitZModType.


Section InvLimitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}).

Fact iloneP : isthread Sys (fun i => 1 : Ob i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : {invlim Sys} := InvLim iloneP.

Fact ilmulP x y : isthread Sys (fun i => 'pi_i x * 'pi_i y).
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
apply/negP => /eqP/(congr1 (fun x => x (invsys_inh Sys))) /= /eqP.
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

Fact ilind_is_multiplicative : multiplicative (ilind Hcomp).
Proof.
split.
- by move=> t u; apply invlimP=> i; rewrite ilindP rmorphM /= !ilindP.
- by apply invlimP=> i; rewrite ilindP !rmorph1.
Qed.
Canonical ilind_multiplicative := AddRMorphism ilind_is_multiplicative.

End UniversalProperty.

End InvLimitRing.


Section InvLimitComRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}).

Fact ilmulC x y : x * y = y * x.
Proof. by apply invlimP=> i; rewrite /= mulrC. Qed.
Canonical invlim_comRingType :=
  Eval hnf in ComRingType (invlim Sys) ilmulC.
Canonical invlimp_comRingType :=
  Eval hnf in ComRingType {invlim Sys} ilmulC.

End InvLimitComRing.


Section InvLimitUnitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}).

Definition ilunit x := `[forall i, 'pi_i x \is a GRing.unit].

Fact inv_isunitP x :
  (forall i, 'pi_i x \is a GRing.unit) -> isthread Sys (fun i => ('pi_i x)^-1).
Proof.
by move=> Hunit i j ilej; rewrite /= rmorphV ?(ilprojE x) // Hunit.
Qed.
Definition ilinv x : {invlim Sys} :=
  if pselect (forall i, 'pi_i x \is a GRing.unit) is left Pf
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
by exists ('pi_i y); rewrite -!rmorphM Hxy Hyx.
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

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Canonical invlim_comUnitRingType :=
  Eval hnf in [comUnitRingType of invlim Sys].
Canonical invlimp_comUnitRingType :=
  Eval hnf in [comUnitRingType of {invlim Sys}].

End InvLimitComUnitRing.


Section InvLimitIDomain.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}).

Fact ilmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> H; case: (altP (x =P 0)) => //= /il_neq0 [i Hi].
move: H; apply contra_eqT => /il_neq0 [j Hj].
have [k ilek jlek] := directedP i j.
have {Hi} /negbTE Hx : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
have {Hj} /negbTE Hy : 'pi_k y != 0.
  move: Hj; apply contra => /eqP/(congr1 (bonding jlek)).
  by rewrite (ilprojE y) raddf0 => ->.
apply/negP => /eqP/(congr1 'pi_k)/eqP.
by rewrite rmorph0 rmorphM mulf_eq0 Hx Hy.
Qed.

Canonical invlim_idomainType :=
  Eval hnf in IdomainType (invlim Sys) ilmul_eq0.
Canonical invlimp_idomainType :=
  Eval hnf in IdomainType {invlim Sys} ilmul_eq0.

End InvLimitIDomain.


Section InvLimitLinear.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}) (r : R).

Fact ilscaleP r x : isthread Sys (fun i => r *: 'pi_i x).
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

Fact ilind_is_linear : linear (ilind Hcomp).
Proof.
by move=> r t u; apply invlimP=> i; rewrite !ilindP !linearP /= !ilindP.
Qed.
Canonical ilind_linear := AddLinear ilind_is_linear.

End UniversalProperty.

End InvLimitLinear.


Section InvLimitLalg.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

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
Canonical ilind_lrmorphism := AddLRMorphism (ilind_is_linear Hcomp).

End UniversalProperty.

End InvLimitLalg.


Section InvLimitAlg.

Variables (disp : unit) (I : dirType disp).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}) (r : R).


Fact ilscaleAr r x y : ilscale r (x * y) = x * ilscale r y.
Proof. by apply invlimP=> i /=; rewrite scalerAr. Qed.
Canonical invlim_algType :=
  Eval hnf in AlgType R (invlim Sys) ilscaleAr.
Canonical invlimp_algType :=
  Eval hnf in AlgType R {invlim Sys} ilscaleAr.

End InvLimitAlg.


Section InvLimitUnitAlg.

Variables (disp : unit) (I : dirType disp).
Variables (R : comUnitRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Canonical invlim_unitalgType := [unitAlgType R of (invlim Sys)].
Canonical invlimp_unitalgType := [unitAlgType R of {invlim Sys}].

End InvLimitUnitAlg.


Section InvLimitField.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Fact invlim_fieldMixin : GRing.Field.mixin_of [unitRingType of {invlim Sys}].
Proof.
move=> x /il_neq0 [i Hi].
rewrite unfold_in /= /ilunit; apply/forallbP => j; rewrite unitfE.
have [k ilek jlek] := directedP i j.
have {Hi} : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
by rewrite -(ilprojE x jlek) fmorph_eq0.
Qed.
Canonical invlim_fieldType :=
  Eval hnf in FieldType (invlim Sys) invlim_fieldMixin.
Canonical invlimp_fieldType :=
  Eval hnf in FieldType {invlim Sys} invlim_fieldMixin.

End InvLimitField.



(** An example to do tests *)
Section CNVars.

Import GRing.Theory.
Open Scope ring_scope.
Variable R : comRingType.

Section Defs.

Variable (n m : nat).
Lemma cnvar_tupleP (T : eqType) (t : seq T) (c : T) :
  size (take m t ++ nseq (m - size t) c) == m.
Proof.
rewrite size_cat size_take size_nseq -/(minn _ _) minnC /minn.
case: ltnP => [/ltnW/subnKC -> //|]; rewrite -subn_eq0 => /eqP ->.
by rewrite addn0.
Qed.
Definition cnvar_tuple : m.-tuple {mpoly R[n]} :=
  Tuple (cnvar_tupleP [tuple 'X_i | i < n] 0).
Definition cnvar p := p \mPo cnvar_tuple.

Fact cnvar_is_rmorphism : rmorphism cnvar.
Proof. repeat split; [exact: rmorphB | exact: rmorphM | exact: rmorph1]. Qed.
Canonical cnvar_additive := Additive cnvar_is_rmorphism.
Canonical cnvar_rmorphism := RMorphism cnvar_is_rmorphism.

Fact cnvar_is_linear : linear cnvar.
Proof. by rewrite /cnvar; exact: linearP. Qed.
Canonical cnvar_linear := AddLinear cnvar_is_linear.
Canonical cnvar_lrmorphism := [lrmorphism of cnvar].

Hypothesis (nlem : (n <= m)%N).
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
by rewrite (ltnNge m n) nlem /= (ltnNge i n) nlei /= nth_nseq if_same.
Qed.

End Defs.

Lemma cnvar_id n : @cnvar n n =1 id.
Proof.
move=> p; rewrite /cnvar.
suff -> : cnvar_tuple n n = [tuple 'X_i | i < n] by rewrite comp_mpoly_id.
apply eq_from_tnth => i.
rewrite tnth_cnvar_tuple // tnth_mktuple; congr ('X_ _).
exact: val_inj.
Qed.

Lemma cnvar_compat i j k :
  (i <= j)%N -> (j <= k)%N -> (@cnvar i j) \o (@cnvar j k) =1 (@cnvar i k).
Proof.
move=> ilej jlek p /=; have ilek := leq_trans ilej jlek.
rewrite /cnvar !(comp_mpolyE p) raddf_sum /=; apply eq_bigr => m _.
rewrite comp_mpolyZ; congr (_ *: _).
rewrite rmorph_prod /=; apply eq_bigr => l _.
rewrite !rmorphX /=; congr (_ ^+ _).
case: (ltnP l i) => [llti | ilel].
- rewrite !tnth_cnvar_tuple ?(leq_trans llti ilej) // => Hlj.
  by rewrite comp_mpolyXU -tnth_nth !tnth_cnvar_tuple.
- rewrite [RHS]tnth_cnvar_tuple0 //.
  case: (ltnP l j) => [lltj|jlel].
  + by rewrite tnth_cnvar_tuple // comp_mpolyXU -tnth_nth tnth_cnvar_tuple0.
  + by rewrite tnth_cnvar_tuple0 // comp_mpoly0.
Qed.


Section InverseSys.

Definition cnvarbond (i j : nat) of (i <= j)%O := @cnvar i j.
Program Definition infpoly_sys := @InvSys _ _ _ cnvarbond 0%N _ _.
Next Obligation. exact: cnvar_id. Qed.
Next Obligation. exact: cnvar_compat. Qed.


Variables (i j : nat) (H : (i <= j)%O).
Fact cnvarbond_is_rmorphism : rmorphism (cnvarbond H).
Proof. exact: cnvar_is_rmorphism. Qed.
Canonical cnvarbond_additive := Additive cnvarbond_is_rmorphism.
Canonical cnvarbond_rmorphism := RMorphism cnvarbond_is_rmorphism.

Fact cnvarbond_is_linear : linear (cnvarbond H).
Proof. exact: cnvar_is_linear. Qed.
Canonical cnvarbond_linear := AddLinear cnvarbond_is_linear.
Canonical cnvarbond_lrmorphism := [lrmorphism of (cnvarbond H)].

End InverseSys.


End CNVars.

Section Tests.

Variable R : comRingType.

Variables (i j : nat) (H : (i <= j)%O).
Check [lrmorphism of (cnvarbond H)].

Check [zmodType of {invlim infpoly_sys R}].
Check [comRingType of {invlim infpoly_sys R}].
Check [lmodType R of {invlim infpoly_sys R}].
Check [algType R of {invlim infpoly_sys R}].

Goal forall (r : R) (x y : {invlim infpoly_sys R}),
  'pi_2 (r *: (x * y)) = 'pi_2 y * 'pi_2 (r *: x).
Proof. by move=> r x y; rewrite linearZ /= mulrC scalerAr. Qed.

End Tests.

Section InfPolyTheory.
Variable R : comRingType.

Fact infpolyXP i :
  isthread (infpoly_sys R)
         (fun n => if ltnP i n is LtnNotGeq Pf then 'X_(Ordinal Pf) else 0).
Proof.
move=> m n mlen /=.
case (ltnP i m) => [iltm|mlei]; case (ltnP i n) => [iltn|nlei].
- by rewrite /cnvarbond/cnvar comp_mpolyXU -tnth_nth tnth_cnvar_tuple.
- by exfalso; have:= leq_trans iltm (leq_trans mlen nlei); rewrite ltnn.
- by rewrite /cnvarbond/cnvar comp_mpolyXU -tnth_nth tnth_cnvar_tuple0.
- by rewrite raddf0.
Qed.
Definition infpolyX i : {invlim infpoly_sys _} := InvLim (infpolyXP i).

End InfPolyTheory.


Section DivCompl.
Open Scope nat_scope.

Lemma modB m n d : 0 < d -> d %| m -> n <= m -> m - n = d - n %% d %[mod d].
Proof.
move=> Hd; rewrite (modn_def n d); case: (edivnP n d) => q r ->.
rewrite Hd /= => rled ddivm Hqr.
rewrite subnDA; apply/eqP. rewrite -(eqn_modDr r); apply/eqP.
rewrite [in RHS]subnK ?modnn; last exact: ltnW.
rewrite subnK; first last.
  by rewrite -(leq_add2l (q * d)) subnKC // (leq_trans _ Hqr) // leq_addr.
move: ddivm => /dvdnP [k ->{m Hqr}].
by rewrite -mulnBl modnMl.
Qed.

Definition Zmn m n : 'Z_n -> 'Z_m := fun i => inZp i.

Variables m n p : nat.
Hypothesis (mgt1 : m > 1) (ngt1 : n > 1).
Hypothesis (mdivn : m %| n).
Lemma Zmn_is_rmorphism : rmorphism (@Zmn m n).
Proof.
repeat split=> [[i Hi] [j Hj]|]; rewrite /= /Zmn /inZp;
    apply val_inj; move: Hi Hj; rewrite /= !Zp_cast // => Hi Hj.
- rewrite !modnDml !modnDmr modn_dvdm //.
  by apply/eqP; rewrite eqn_modDl modB //; apply: ltnW.
- by rewrite modn_dvdm // modnMml modnMmr.
Qed.

Lemma comp_Zmn : @Zmn m n \o @Zmn n p =1 @Zmn m p.
Proof.
move=> i /=; apply val_inj => /=.
rewrite (Zp_cast ngt1) (Zp_cast mgt1).
rewrite (modn_def i n); case: (edivnP i n) => {i} q r -> /= Hr.
by move: mdivn => /dvdnP [k ->]; rewrite mulnA -modnDml modnMl add0n.
Qed.

End DivCompl.

Definition padic_bond (p : nat) of (prime p) :=
  fun (i j : nat) of (i <= j)%O => @Zmn (p ^ i.+1)%N (p ^ j.+1)%N.

Section Padics.

Variable (p : nat).
Local Notation Z j := 'Z_(p ^ j.+1).

Hypothesis (p_pr : prime p).
Lemma expgt1 l : (1 < p ^ (l.+1))%N.
Proof.
apply: (leq_trans (prime_gt1 p_pr)).
by rewrite -{1}(expn1 p) leq_exp2l // prime_gt1.
Qed.
Lemma expgt0 l : (0 < p ^ (l.+1))%N.
Proof. exact: ltn_trans _ (expgt1 l). Qed.

Lemma truncexp l : (Zp_trunc (p ^ l.+1)).+2 = (p ^ l.+1)%N.
Proof. by rewrite Zp_cast // expgt1. Qed.

Lemma expN1lt n : (p ^ n.+1 - 1 < p ^ n.+1)%N.
Proof.
have := expgt1 n; case: (p ^ _)%N => // k _.
by rewrite subSS subn0 ltnS.
Qed.

Local Lemma expdiv n i j : (i <= j)%O -> (n ^ i.+1 %| n ^ j.+1)%N.
Proof.
rewrite leEnat -ltnS => Hij;
by rewrite -(subnK Hij) expnD dvdn_mull.
Qed.

Program Definition padic_invsys :=
  InvSys (bonding := fun (i j : nat) (H : (i <= j)%O) => padic_bond p_pr H)
         0%N _ _.
Next Obligation. by move=> x; apply valZpK. Qed.
Next Obligation. exact: comp_Zmn (expgt1 i) (expgt1 j) (expdiv _ _). Qed.

Variables (i j : nat) (H : (i <= j)%O).
Lemma bond_is_rmorphism : rmorphism (padic_bond p_pr H).
Proof. exact: Zmn_is_rmorphism (expgt1 i) (expgt1 j) (expdiv _ _). Qed.
Canonical bond_additive := Additive bond_is_rmorphism.
Canonical bond_rmorphism := RMorphism bond_is_rmorphism.

End Padics.

Definition padic_int (p : nat) (p_pr : prime p) := {invlim padic_invsys p_pr}.


Section PadicTheory.

Variables (p : nat) (p_pr : prime p).
Implicit Type x y : padic_int p_pr.

Lemma padic_unit x : (x \is a GRing.unit) = ('pi_0%N x != 0).
Proof.
rewrite unfold_in /= /ilunit; apply/forallbP/idP => [/(_ 0%N) | /= Hx i].
- by apply/memPn: ('pi_0%N x); rewrite unitr0.
- have:= leq0n i; rewrite -leEnat => Hi.
  move: (ilprojE x Hi) Hx; rewrite {Hi} /padic_bond /Zmn => <-.
  move: ('pi_i x); rewrite {x} expn1 -(pdiv_id p_pr) => m /=.
  rewrite -{2}(natr_Zp m) unitZpE ?expgt1 ?pdiv_id //.
  rewrite /inZp /= -(natr_Zp (Ordinal _)) /= -unitfE unitFpE //.
  rewrite pdiv_id // in m |- *.
  rewrite (@Zp_cast p) ?prime_gt1 // coprime_modr.
  exact: coprime_expl.
Qed.

Fact padic_mul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
case: (altP (x =P 0)) => //= /il_neq0 [/= i Hneq0] Hxy.
apply/eqP/invlimP=> /= j.
move: Hxy => /(congr1 'pi_(i+j)%N); rewrite raddf0 rmorphM /=.
move: Hneq0.
have:= leq_addr i j; rewrite -leEnat => Hij; rewrite -(ilprojE y Hij).
have:= leq_addr j i; rewrite -leEnat => Hji; rewrite -(ilprojE x Hji).
rewrite /padic_bond /Zmn {Hij Hji} [(j + i)%N]addnC.
move: ('pi_(i + j)%N x) ('pi_(i + j)%N y) => {x y} [x Hx] [y Hy].
rewrite /inZp /= -(natr_Zp (Ordinal _)) /=.
rewrite truncexp // (Zp_nat_mod (expgt1 p_pr i)) => xmod.
have {xmod} xmod : (x %% p^(i.+1) != 0)%N.
  move: xmod; apply contra => /eqP Heq.
  by rewrite Zp_nat; apply/eqP/val_inj; rewrite /= truncexp.
move=> /(congr1 val); rewrite /= (truncexp p_pr (i + j)) => /eqP xymod.
apply val_inj; rewrite /= truncexp // => {Hx Hy}.
have xn0 : (0 < x)%N.
  by apply/contraR: xmod; rewrite -leqNgt leqn0 => /eqP ->; rewrite mod0n.
case: (ltnP 0%N y)=> [yn0|]; last by rewrite leqn0 => /eqP ->; rewrite mod0n.
have xyn0 : (0 < x * y)%N by rewrite muln_gt0 xn0 yn0.
apply/eqP; rewrite -/(dvdn _ _) pfactor_dvdn //.
move: xymod; rewrite -/(dvdn _ _) pfactor_dvdn // lognM //.
move: xmod;  rewrite -/(dvdn _ _) pfactor_dvdn // -leqNgt => logx.
by apply contraLR; rewrite -!leqNgt; exact: leq_add.
Qed.
Canonical padic_int_idomainType :=
  Eval hnf in IdomainType (padic_int p_pr) padic_mul_eq0.

End PadicTheory.



Section Tests.
Variables (p : nat) (p_pr : prime p).
Canonical padic_unit_ring := Eval hnf in [unitRingType of padic_int p_pr].


Fact padicN1_thread :
  isthread (padic_invsys p_pr) (fun n => inord (p ^ n.+1 - 1)).
Proof.
move=> m n mlen /=; rewrite /padic_bond /Zmn; apply val_inj => /=.
rewrite !inordK truncexp // ?expN1lt //.
rewrite modB; try exact: expgt0; try exact: expdiv.
by rewrite (modn_small (expgt1 _ _)) // modn_small // expN1lt.
Qed.
Definition ZpN1 : {invlim padic_invsys p_pr} := InvLim padicN1_thread.

Lemma ZpN1E : ZpN1 = -1.
Proof.
apply invlimP => /= n; apply val_inj => /=.
rewrite inordK truncexp // ?expN1lt //.
by rewrite (modn_small (expgt1 _ _)) // modn_small // expN1lt.
Qed.

End Tests.
