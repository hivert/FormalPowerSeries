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

Require Import natbar.

Import Order.Def.
Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'invlim' S }"
         (at level 0, format "{ 'invlim'  S }").
Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "\pi" (at level 0, format "\pi").

Reserved Notation "''pi_' i" (at level 8, i at level 2, format "''pi_' i").

Reserved Notation "\Sum_( i : t ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i  :  t )  F").
Reserved Notation "\Sum_( i ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i )  F").


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
Section InverseSystem.

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

Definition isthread of invsys := fun thr : forall i, Ob i =>
  forall i j, forall (Hij : i <= j), bonding Hij (thr j) = thr i.
Definition iscompat of invsys := fun T (mors : forall i, T -> Ob i) =>
  forall i j, forall (Hij : i <= j), bonding Hij \o mors j =1 mors i.

End InverseSystem.



(***************************************************************************)
(** Interface for inverse limits                                           *)
(*                                                                         *)
(***************************************************************************)
Module InvLim.

Section Defs.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.

Section Mixin.

Variable Tinv : Type.

Record mixin_of := Mixin {
  invlim_proj : forall i, Tinv -> Ob i;
  invlim_ind  : forall (T : Type) (f : forall i, T -> Ob i),
      (iscompat Sys f) -> T -> Tinv;
  _ : iscompat Sys invlim_proj;
  _ : forall T (f : forall i, T -> Ob i) (Hcomp : iscompat Sys f),
      forall i, invlim_proj i \o invlim_ind Hcomp =1 f i;
  _ : forall T (f : forall i, T -> Ob i) (Hcomp : iscompat Sys f),
      forall (ind : T -> Tinv),
        (forall i, invlim_proj i \o ind =1 f i) ->
        ind =1 invlim_ind Hcomp
  }.

End Mixin.

Notation class_of := mixin_of.

Record invLimType := InvLimTypePack {
  invlim_sort :> Type;
  invlim_class : class_of invlim_sort
}.

Variable ilT : invLimType.
Definition pi_phant of phant ilT := invlim_proj (invlim_class ilT).
Local Notation "\pi" := (pi_phant (Phant ilT)).
Definition ind_phant of phant ilT := invlim_ind (invlim_class ilT).
Local Notation "\ind" := (ind_phant (Phant ilT)).

Lemma proj_compat : iscompat Sys \pi.
Proof. by rewrite /pi_phant; case: ilT => /= [Tinv []]. Qed.

Lemma ind_commute T (f : forall i, T -> Ob i) (Hcomp : iscompat Sys f) :
  forall i, \pi i \o \ind Hcomp =1 f i.
Proof. by rewrite /pi_phant /ind_phant; case: ilT => /= [Tinv []]. Qed.

Lemma ind_uniq T (f : forall i, T -> Ob i) (Hcomp : iscompat Sys f) :
  forall (ind : T -> ilT),
    (forall i, \pi i \o ind =1 f i) -> ind =1 \ind Hcomp.
Proof.
rewrite /pi_phant /ind_phant.
case: ilT => /= [Tinv [pi /= ind comp comm uniq]] indT commT t.
by apply: uniq; apply commT.
Qed.

Lemma invlimE (x y : ilT) : (forall i, \pi i x = \pi i y) -> x = y.
Proof.
move=> Heq.
pose fx : forall i : I, unit -> Ob i := fun i tt => \pi i x.
have compf : iscompat Sys fx.
  rewrite /fx => i j le_ij tt /=.
  by rewrite -/((bonding le_ij \o \pi j) x) proj_compat.
pose ind z : unit -> ilT := fun tt => z.
have Huniqy : forall i, \pi i \o ind y =1 fx i.
  by move=> i tt /=; rewrite /ind /fx Heq.
have Huniqx : forall i, \pi i \o ind x =1 fx i.
  by move=> i tt /=; rewrite /ind /fx Heq.
move: (ind_uniq compf Huniqx tt) (ind_uniq compf Huniqy tt).
by rewrite /ind /ind_phant => -> ->.
Qed.

Lemma from_tread_spec (thr : forall i : I, Ob i) :
  isthread Sys thr -> { t : ilT | forall i, \pi i t = thr i }.
Proof.
rewrite /isthread => Hhtr.
pose f : forall i : I, unit -> Ob i := fun i tt => thr i.
have compf : iscompat Sys f by rewrite /f => i j le_ij tt /=.
exists (\ind compf tt) => i.
by rewrite -/((\pi i \o \ind compf) tt) ind_commute.
Qed.

End Defs.

Notation "\pi" := (pi_phant (Phant _)).
Notation "''pi_' i" := (pi_phant (Phant _) i).
Notation "\ind" := (ind_phant (Phant _)).




(**** Implementation ************)


Record invlim := InvLim { ilthr :> forall i, Ob i; _ : isthread Sys ilthr; }.

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

Definition ilproj i : {invlim Sys} -> Ob i := (ilthr (Sys := Sys))^~ i.

Lemma ilprojE x :
  forall i j, forall (Hij : i <= j), bonding Hij (ilproj j x) = ilproj i x.
Proof. by case: x. Qed.

Lemma ilprojP : iscompat Sys ilproj.
Proof. by move=> i j Hij [thr Hthr]; apply Hthr. Qed.

Local Notation "''pi_' i" := (ilproj i).

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
Notation "'pi_ i" := (ilproj i) : ring_scope.


(****************************************************************************)
(** Inverse limits in various algebraic categories                          *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)
Open Scope ring_scope.
Import GRing.Theory.

Section InvLimitEqType.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.

Variable Sys : invsys bonding.
Implicit Type x y : {invlim Sys}.

Lemma invlimPn x y : reflect (exists i, 'pi_i x != 'pi_i y) (x != y).
Proof.
apply (iffP idP) => [neq|[i]]; last by apply/contra => /eqP ->.
apply/asboolP; rewrite asbool_existsNb; apply/contra: neq => /asboolP Hx.
by apply/eqP/invlimP => /= i; apply/eqP.
Qed.

End InvLimitEqType.


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



(***************************************************************************)
(** Valuation in inverse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Ob : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : invsys bonding.

Implicit Type (x y : {invlim Sys}).


Definition valuat x : natbar :=
  if altP (x =P 0) is AltFalse Pf then Nat (ex_minn (il_neq0 Pf))
  else Inf.

Variant valuat_spec x : natbar -> Type :=
  | ValNat n of 'pi_n x != 0 & (forall i, (i < n)%N -> 'pi_i x = 0) :
      valuat_spec x (Nat n)
  | ValInf of x = 0 : valuat_spec x Inf.

Lemma valuatP x : valuat_spec x (valuat x).
Proof.
rewrite /valuat; case (altP (x =P 0)) => [Pf|NPf]; first exact: ValInf.
case: ex_minnP => v Hv vmin; apply ValNat => [|i iv]; first exact: Hv.
by apply/contraTeq: iv; rewrite -leqNgt; apply vmin.
Qed.

Lemma lt_valuatP x n : reflect ('pi_n x = 0) (Nat n < valuat x)%O.
Proof.
apply (iffP idP); case: valuatP => [v Hv vmin /= |->] //.
- by rewrite ltEnatbar; apply vmin.
- apply contra_eqT; rewrite ltEnatbar -leqNgt => vlen.
  apply/contra: Hv => /eqP/(congr1 (bonding vlen)).
  by rewrite (ilprojE x) raddf0 => ->.
Qed.

Lemma le_valuatP x n :
  reflect (forall i, (i < n)%N -> 'pi_i x = 0) (Nat n <= valuat x)%O.
Proof.
apply (iffP idP).
- case: valuatP => [v Hv vmin /= |->] //.
  by rewrite leEnatbar => nlev i /leq_trans/(_ nlev); apply vmin.
- case: n => // n; first exact: le0bar.
  move=> /(_ n)/(_ (ltnSn _)) /lt_valuatP.
  by case: (valuat x)=> // v; rewrite ltEnatbar leEnatbar.
Qed.

Lemma proj_gt_valuat x n : (Nat n >= valuat x)%O = ('pi_n x != 0).
Proof. by apply negb_inj; rewrite negbK -ltNge; apply/lt_valuatP/eqP. Qed.

Lemma valuatNatE x n :
  'pi_n x != 0 -> (forall i, (i < n)%N -> 'pi_i x = 0) -> valuat x = Nat n.
Proof.
move=> Hn nmin; apply le_anti; rewrite proj_gt_valuat Hn /=.
exact/le_valuatP.
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite raddf0 eqxx. Qed.

Lemma valuat0P x : (valuat x == Inf) = (x == 0).
Proof.
apply/eqP/eqP=> [valx|->]; last exact: valuat0.
by apply/invlimP=> i; rewrite raddf0; apply/lt_valuatP; rewrite valx.
Qed.

Lemma valuatN x : valuat (- x) = valuat x.
Proof.
case: (valuatP x) => [vN HvN vnmiN /= | ->]; last by rewrite oppr0 valuat0.
apply valuatNatE; first by rewrite raddfN oppr_eq0.
by move=> i /vnmiN; rewrite raddfN /= => ->; rewrite oppr0.
Qed.

Lemma valuatD x1 x2 :
  (valuat x1 `&` valuat x2 <= valuat (x1 + x2))%O.
Proof.
wlog v1lev2 : x1 x2 / (valuat x1 <= valuat x2)%O.
  move=> Hlog; case: (leP (valuat x1) (valuat x2)) => [|/ltW]/Hlog//.
  by rewrite addrC meetC.
rewrite (meet_idPl v1lev2); move: v1lev2.
case: (valuatP x1)=> [v1 Hv1 v1min|->]; last by rewrite add0r.
case: (valuatP x2)=> [v2 Hv2 v2min|->]; last by rewrite addr0 (valuatNatE Hv1).
rewrite leEnatbar => le12.
apply/le_valuatP => i Hi; rewrite raddfD /= v1min ?v2min ?addr0 //.
exact: leq_trans Hi le12.
Qed.
Lemma valuat_sum I r P (F : I ->  {invlim Sys}) :
  (\meet_(i <- r | P i) valuat (F i) <= valuat (\sum_(i <- r | P i) F i))%O.
Proof.
apply: (big_ind2 (fun x v => v <= valuat x)%O); rewrite ?valuat0 //=.
by move=> x1 v1 x2 v2 H1 H2; apply: (le_trans (leI2 _ _) (valuatD x1 x2)).
Qed.

Lemma valuatB s1 s2 :
  (valuat s1 `&` valuat s2 <= valuat (s1 - s2))%O.
Proof. by have:= valuatD s1 (-s2); rewrite valuatN. Qed.

Lemma valuatDr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 + s2) = valuat s1.
Proof.
case: (valuatP s2) => [v2 _   v2min|-> _]; last by rewrite addr0.
case: (valuatP s1) => [v1 Hv1 v1min|->]; last by rewrite ltIbar.
rewrite ltEnatbar => v12.
apply valuatNatE=> [|n nv1]; rewrite raddfD /= v2min ?addr0 // ?v1min //.
exact: ltn_trans nv1 v12.
Qed.

Lemma valuatBr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 - s2) = valuat s1.
Proof. by rewrite -(valuatN s2) => /valuatDr. Qed.
Lemma valuatBl s1 s2 :
  (valuat s2 < valuat s1)%O -> valuat (s1 - s2) = valuat s2.
Proof. by rewrite -(valuatN s2) addrC => /valuatDr. Qed.

End Valuation.


From mathcomp Require Import finmap.

Section CommHugeOp.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j : I, (i <= j)%O -> (Ob j) -> (Ob i).
Variable Sys : invsys bonding.

Variable (C : choiceType).
Variables (idx : {invlim Sys}) (op : Monoid.com_law idx).

Implicit Type F : C -> {invlim Sys}.
Implicit Types (x y z t : {invlim Sys}).

Definition invar i x := forall s, 'pi_i (op x s) = 'pi_i s.
Definition is_ilopable F :=
  forall i, exists s : seq C, forall c, c \notin s -> invar i (F c).
Lemma ilopable_spec F :
  is_ilopable F ->
  forall i, { f : {fset C} | f =i predC (fun c => `[< invar i (F c)>]) }.
Proof.
move=> H i; move/(_ i): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq c <- s | ~~ `[< invar i (F c)>]]) => c.
rewrite seq_fsetE !inE mem_filter.
by case: (boolP `[< _>]) => //=; apply contraR => /Hs/asboolT.
Qed.
Definition ilopable F (sm : is_ilopable F) c :=
  let: exist fs _ := ilopable_spec sm c in fs.

Lemma ilopableP F (sm : is_ilopable F) i c :
  reflect (invar i (F c)) (c \notin (ilopable sm i)).
Proof.
rewrite /ilopable; apply (iffP negP); case: ilopable_spec => f Hf.
- by rewrite Hf inE => /negP; rewrite negbK => /asboolW.
- by rewrite Hf inE => H; apply/negP; rewrite negbK; apply asboolT.
Qed.

Lemma ilopable_subset F (sm : is_ilopable F) i j :
  (i <= j)%O -> (ilopable sm i `<=` ilopable sm j)%fset.
Proof.
move=> ilej.
apply/fsubsetP => c; apply/contraLR => /ilopableP Hinv.
by apply/ilopableP => x; rewrite -!(ilprojE _ ilej) Hinv.
Qed.

Fact ilopable_istrhead F (sm : is_ilopable F) :
  isthread Sys (fun i => 'pi_i (\big[op/idx]_(c <- ilopable sm i) F c)).
Proof.
move=> i j Hij; rewrite ilprojE.
rewrite (bigID (fun c => `[< invar i (F c)>])) /=.
set X := (X in op _ X); set Y := (Y in _ = _ Y).
have {X} -> : X = Y.
  rewrite {}/X {}/Y; apply eq_fbigl_cond => c.
  rewrite !inE andbT; apply negb_inj; rewrite negb_and negbK.
  case: (boolP (c \in (ilopable sm j))) => /= Hc.
  - by apply/asboolP/idP=> /ilopableP //; apply.
  - suff -> : c \notin (ilopable sm i) by [].
    by apply/contra: Hc; apply: (fsubsetP (ilopable_subset sm Hij)).
elim: (X in \big[op/idx]_(i <- X | _) _) => [| s0 s IHs].
  by rewrite big_nil Monoid.mul1m.
rewrite big_cons /=; case: asboolP => [|]; last by rewrite IHs.
by rewrite -Monoid.mulmA {1}/invar => ->.
Qed.

Definition HugeOp F : {invlim Sys} :=
  if pselect (is_ilopable F) is left sm
  then InvLim (ilopable_istrhead sm)
  else idx.

Local Notation "\Op_( c ) F" := (HugeOp (fun c => F)) (at level 0).

(*
Lemma coefsHugeOp F i (S : {fset C}) :
  is_ilopable F ->
  subpred (predC (mem S)) (fun c => `[< invar i (F c)>]) ->
  'pi_i (\Op_( c ) (F c)) = 'pi_i (\big[op/idx]_(c <- S) (F c)).
Proof.
rewrite /HugeOp=> Hop Hsub; case: pselect; last by move=> /(_ Hop).
move=> /= {Hop} Hop.
transitivity ('pi_i (\big[op/idx]_(c <- S | c \in ilopable Hop i) F c));
  first last.
  

rewrite [in RHS](bigID [pred c | `[< invar i (F c)>]]) /=.
  rewrite [X in op _ X]big1 ?addr0; first last.
  move=> j /andP [].

   rewrite negbK => /eqP.
rewrite -[RHS]big_filter; apply: perm_big.
apply: (uniq_perm (fset_uniq _) (filter_uniq _ (enum_finpred_uniq _))) => i.
rewrite ilopableE mem_filter inE enum_finpredE.
 by case: (boolP (_ == 0)) => // /Hsub /= ->.
Qed.
 *)

End CommHugeOp.
