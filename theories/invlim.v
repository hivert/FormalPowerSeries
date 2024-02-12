(** Inverse limits *)
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
(** * Inverse Limits

- {invlim Sys} == a default implementation of the inverse limits of [Sys]
*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order finmap bigop.

Require Import natbar directed.


Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'invlim' S }"
         (at level 0, format "{ 'invlim'  S }").
Reserved Notation "''pi_' i" (at level 8, i at level 2, format "''pi_' i").
Reserved Notation "''pi[' T ']_' i" (at level 8, i at level 2).
Reserved Notation "''ind[' T ']'" (at level 8).

Reserved Notation "\Sum_( i : t ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i  :  t )  F").
Reserved Notation "\Sum_( i ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i )  F").


(***************************************************************************)
(** Inverse systems and inverse limits                                     *)
(*                                                                         *)
(***************************************************************************)
Section InverseSystem.

Variables (disp : unit) (I : porderType disp).

(** Objects and bonding morphisms of the inverse system at left outside    *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Obj : I -> Type.
Variable bonding : (forall i j, i <= j -> Obj j -> Obj i).
Record is_invsys : Type := IsInvSys {
      invsys_inh : I;
      invsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      invsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hij) \o (bonding Hjk) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition isthread of is_invsys := fun thr : forall i, Obj i =>
  forall i j, forall (Hij : i <= j), bonding Hij (thr j) = thr i.

Definition cone of is_invsys := fun T (mors : forall i, T -> Obj i) =>
  forall i j, forall (Hij : i <= j), bonding Hij \o mors j =1 mors i.

Lemma coneE Sys T (mors : forall i, T -> Obj i) : cone Sys mors ->
  forall i j (Hij : i <= j) x, bonding Hij (mors j x) = mors i x.
Proof. by rewrite /cone => H i j le_ij x; rewrite -(H i j le_ij). Qed.

Lemma cone_thr Sys T (mors : forall i, T -> Obj i) :
  cone Sys mors -> forall t : T, isthread Sys (mors ^~ t).
Proof. by rewrite /cone => Hf t i j Hij; apply: Hf. Qed.

End InverseSystem.


(***************************************************************************)
(** Interface for inverse limits                                           *)
(*                                                                         *)
(***************************************************************************)
Open Scope ring_scope.


#[key="ilT"]
HB.mixin Record isInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj j -> Obj i)
    (Sys : is_invsys bonding)
  ilT of Choice ilT := {
    invlim_proj : forall i, ilT -> Obj i;
    invlim_ind  : forall (T : Type) (f : forall i, T -> Obj i),
      (cone Sys f) -> T -> ilT;
    ilprojP : cone Sys invlim_proj;
    ilind_commute : forall T (f : forall i, T -> Obj i) (Hcone : cone Sys f),
      forall i, invlim_proj i \o invlim_ind T f Hcone =1 f i;
    ilind_uniq : forall T (f : forall i, T -> Obj i) (Hcone : cone Sys f),
      forall (ind : T -> ilT),
        (forall i, invlim_proj i \o ind =1 f i) ->
        ind =1 invlim_ind T f Hcone
  }.

#[short(type="invLimType")]
HB.structure Definition InvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj j -> Obj i)
    (Sys : is_invsys bonding)
  := {
    ilT of isInvLim disp I Obj bonding Sys ilT
    & Choice ilT
  }.



Section InternalTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.

Local Notation "\pi" := (invlim_proj (s := ilT)).
Local Notation "\ind" := (invlim_ind (s := ilT) _ _).

Lemma ilprojE (x : ilT) :
  forall i j, forall (Hij : i <= j), bonding Hij (\pi j x) = \pi i x.
Proof. by move=> i j Hij; rewrite [LHS]ilprojP. Qed.

Lemma piindE  T (f : forall i, T -> Obj i) (Hcone : cone Sys f) i x :
  \pi i (\ind Hcone x) = f i x.
Proof. exact: ilind_commute. Qed.

End InternalTheory.

Arguments ilprojP {disp I Obj bonding} [Sys].

Notation "''pi_' i" := (invlim_proj i).
Notation "''pi[' T ']_' i" := (invlim_proj (s := T) i) (only parsing).
Notation "''ind[' T ']'" := (invlim_ind (s := T) _ _) (only parsing).
Notation "''ind'" := ('ind[ _ ]).


Section Theory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.

Lemma invlimE (x y : ilT) : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq.
pose fx : forall i : I, unit -> Obj i := fun i tt => 'pi_i x.
have compf : cone Sys fx.
  by rewrite /fx => i j le_ij tt /=; rewrite ilprojE.
pose ind z : unit -> ilT := fun tt => z.
have Huniqy i : 'pi_i \o ind y =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
have Huniqx i : 'pi_i \o ind x =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
move: (ilind_uniq _ _ compf _ Huniqx tt) (ilind_uniq _ _ compf _ Huniqy tt).
by rewrite /ind => -> ->.
Qed.

Lemma from_thread_spec (thr : forall i : I, Obj i) :
  isthread Sys thr -> { t : ilT | forall i, 'pi_i t = thr i }.
Proof.
rewrite /isthread => Hhtr.
pose f : forall i : I, unit -> Obj i := fun i tt => thr i.
have compf : cone Sys f by rewrite /f => i j le_ij tt /=.
by exists ('ind compf tt) => i; rewrite piindE.
Qed.
Definition ilthr thr (Hthr : isthread Sys thr) :=
  let: exist res _ := from_thread_spec Hthr in res.

Lemma ilthrP thr (Hthr : isthread Sys thr) i : 'pi_i (ilthr Hthr) = thr i.
Proof. by rewrite /ilthr; case: from_thread_spec. Qed.

Lemma invlim_exE (x y : ilT) :
  (forall i, exists2 i0, i0 >= i & 'pi_i0 x = 'pi_i0 y) -> x = y.
Proof.
move=> Heq; apply invlimE => i.
move: Heq => /( _ i) [i0 le_ii0] /(congr1 (bonding le_ii0)).
by rewrite !ilprojE.
Qed.

End Theory.
Arguments ilthr {disp I Obj bonding Sys ilT thr}.


Section InvLimitDirected.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.

Lemma invlim_geE b (x y : ilT) :
  (forall i, i >= b -> 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq; apply invlim_exE => i.
by have:= directedP i b => [][j le_ij {}/Heq Heq]; exists j.
Qed.

End InvLimitDirected.
Arguments invlim_geE {disp I Obj bonding Sys ilT}.


Section InvLimitEqType.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> eqType.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.

Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.
Implicit Type x y : ilT.

Lemma invlimPn x y : reflect (exists i, 'pi_i x != 'pi_i y) (x != y).
Proof.
apply (iffP idP) => [neq|[i]]; last by apply/contra => /eqP ->.
apply/asboolP; rewrite asbool_existsNb; apply/contra: neq => /asboolP Hx.
by apply/eqP/invlimE => /= i; apply/eqP.
Qed.

Lemma invlim_is_surj :
  (forall i (u : Obj i), exists x, 'pi[ilT]_i x = u)
  ->
  (forall i j (le_ij : i <= j) (u : Obj i), exists v, bonding le_ij v = u).
Proof.
move=> Hsurj i j le_ij u; have [x pix] := Hsurj i u.
by exists ('pi_j x); rewrite ilprojE.
Qed.

(* TODO: prove the reciprocal statement
   This seems to need some strong form of choice axiom *)
Lemma invlim_surj_section :
  (forall i (u : Obj i), exists x, 'pi[ilT]_i x = u) ->
  (exists f, forall i (u : Obj i), 'pi[ilT]_i (f i u) = u).
Proof.
move=> H.
have {H}/choice[f Hf] :
  forall p : {i & Obj i}, exists x, 'pi[ilT]_(projT1 p) x = projT2 p.
  by move=> [i u] /=.
by exists (fun i u => f (existT Obj i u)) => i u; apply: (Hf (existT Obj i u)).
Qed.

End InvLimitEqType.



(****************************************************************************)
(**  Interface for inverse limits in various algebraic categories           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

#[key="ilT"]
HB.mixin Record isNmoduleInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT & GRing.Nmodule ilT := {
  ilproj_is_semi_additive :
    forall i, semi_additive ('pi[ilT]_i)
  }.
#[short(type="nmodInvLimType")]
HB.structure Definition NmodInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of InvLim disp Sys ilT
    & isNmoduleInvLim disp I Obj bonding Sys ilT
    & GRing.Nmodule ilT
  }.

Section NmodInvLimTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> nmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : nmodInvLimType Sys.
Implicit Type x y : ilT.

#[export] HB.instance Definition _ i :=
  GRing.isSemiAdditive.Build ilT (Obj i) _ (ilproj_is_semi_additive i).

(** The universal induced map is a N-module morphism *)
Section UniversalProperty.

Variable (T : nmodType) (f : forall i, {additive T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_semi_additive : semi_additive ('ind[ilT] Hcone).
Proof.
by split => [| /= t u]; apply invlimE=> j; rewrite raddf /= !piindE raddf.
Qed.
#[export] HB.instance Definition _ :=
  GRing.isSemiAdditive.Build T ilT _ ilind_is_semi_additive.

End UniversalProperty.

Lemma il_neq0 x : x != 0 -> exists i, 'pi_i x != 0.
Proof. by move/invlimPn=> [i]; rewrite raddf0 => Hi; exists i. Qed.

End NmodInvLimTheory.


#[key="ilT"]
HB.mixin Record isZmoduleInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of NmodInvLim disp Sys ilT & GRing.Zmodule ilT := {
    (** Capture zmodType on Obj*)
   }.
#[short(type="zmodInvLimType")]
HB.structure Definition ZmodInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of NmodInvLim disp Sys ilT
    & isZmoduleInvLim disp I Obj bonding Sys ilT
    & GRing.Zmodule ilT
  }.

Section ZmodInvLimTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : zmodInvLimType Sys.
Implicit Type x y : ilT.

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_additive : additive ('ind[ilT] Hcone).
Proof. exact: raddfB. Qed.
#[export] HB.instance Definition _ :=
  GRing.isAdditive.Build T ilT _ ilind_is_additive.

End UniversalProperty.
End ZmodInvLimTheory.


#[key="ilT"]
HB.mixin Record isSemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT & GRing.SemiRing ilT := {
  ilproj_is_multiplicative :
    forall i, multiplicative ('pi[ilT]_i)
  }.
#[short(type="semiRingInvLimType")]
HB.structure Definition SemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of NmodInvLim disp Sys ilT
    & isSemiRingInvLim disp I Obj bonding Sys ilT
    & GRing.SemiRing ilT
  }.

Section SemiRingInvLimTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> semiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : semiRingInvLimType Sys.
Implicit Type x y : ilT.

#[export] HB.instance Definition _ i :=
  GRing.isMultiplicative.Build ilT (Obj i) _ (ilproj_is_multiplicative i).

(** The universal induced map is a ring morphism *)
Section UniversalProperty.

Variable (T : semiRingType) (f : forall i, {rmorphism T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_multiplicative : multiplicative ('ind[ilT] Hcone).
Proof.
by split => [/= t x|]; apply invlimE=> i;
  rewrite !piindE ?rmorph1 ?rmorphM //= !piindE.
Qed.
#[export] HB.instance Definition _ :=
  GRing.isMultiplicative.Build T ilT _ ilind_is_multiplicative.

End UniversalProperty.

Lemma il_neq1 x : x != 1 -> exists i, 'pi_i x != 1.
Proof. by move/invlimPn=> [i]; rewrite rmorph1 => Hi; exists i. Qed.

End SemiRingInvLimTheory.


(** No capture needed since Ring is the join of SemiRing & Zmodule *)
#[short(type="ringInvLimType")]
HB.structure Definition RingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of SemiRingInvLim disp Sys ilT
    & ZmodInvLim disp Sys ilT
  }.


#[key="ilT"]
HB.mixin Record isComSemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture comSemiRingType on Obj*)
  }.
#[short(type="comSemiRingInvLimType")]
HB.structure Definition ComSemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of SemiRingInvLim disp Sys ilT
    & isComSemiRingInvLim disp I Obj bonding Sys ilT
    & GRing.ComSemiRing ilT
  }.


(** No capture needed since ComRing is the join of Ring & ComSemiRing*)
#[short(type="comRingInvLimType")]
HB.structure Definition ComRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of RingInvLim disp Sys ilT
    & ComSemiRingInvLim disp Sys ilT
  }.


(** Just the join of UnitRing and RingInvLim *)
#[short(type="Unit_RingInvLimType")]
HB.structure Definition Unit_RingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of RingInvLim disp Sys ilT
    & GRing.UnitRing ilT
  }.


#[key="ilT"]
HB.mixin Record isUnitRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture unitRingType on Obj*)
  }.
#[short(type="unitRingInvLimType")]
HB.structure Definition UnitRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of RingInvLim disp Sys ilT
    & isUnitRingInvLim disp I Obj bonding Sys ilT
    & GRing.UnitRing ilT
  }.

Section InvLimUnitRingTheory.

Variables
    (disp : unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding).
Variable ilT : unitRingInvLimType Sys.

Lemma ilunitP (x : ilT) :
  reflect (forall i, 'pi_i x \is a GRing.unit) (x \is a GRing.unit).
Proof.
apply (iffP idP) => [xunit i | H].
   exact: (rmorph_unit ('pi[ilT]_i : {rmorphism ilT -> Obj i}) xunit).
have invthr : isthread Sys (fun i => ('pi_i x)^-1).
  by move=> i j ilej; rewrite /= rmorphV ?(ilprojE x) // H.
apply/unitrP; exists (ilthr invthr).
split; apply: invlimE => i; rewrite rmorph1 rmorphM /= ilthrP.
- exact: (mulVr (H i)).
- exact: (mulrV (H i)).
Qed.

End  InvLimUnitRingTheory.


(** No capture needed since ComUnitRing is the join of ComRing & UnitRing *)
#[short(type="comUnitRingInvLimType")]
HB.structure Definition ComUnitRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of ComRingInvLim _ Sys ilT
    & UnitRingInvLim _ Sys ilT
  }.


#[key="ilT"]
HB.mixin Record isIDomainInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture idomainType on Obj*)
  }.
#[short(type="idomainInvLimType")]
HB.structure Definition IDomainInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of ComUnitRingInvLim disp Sys ilT
    & isIDomainInvLim disp I Obj bonding Sys ilT
    & GRing.IntegralDomain ilT
  }.


#[key="ilT"]
HB.mixin Record isFieldInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture fieldType on Obj*)
  }.
#[short(type="fieldInvLimType")]
HB.structure Definition FieldRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of IDomainInvLim disp Sys ilT
    & isFieldInvLim disp I Obj bonding Sys ilT
    & GRing.Field ilT
  }.


#[key="ilT"]
HB.mixin Record isLmodInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT & GRing.Lmodule R ilT := {
  ilproj_is_linear :
    forall i, linear ('pi[ilT]_i)
  }.
#[short(type="lmodInvLimType")]
HB.structure Definition LmodInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of ZmodInvLim _ Sys ilT
    & isLmodInvLim R disp I Obj bonding Sys ilT
    & GRing.Lmodule R ilT
  }.

Section LmodInvLimTheory.

Variable (R : ringType).
Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : lmodInvLimType Sys.

#[export] HB.instance Definition _ i :=
  GRing.isLinear.Build R ilT (Obj i) _ _ (ilproj_is_linear i).

(** The universal induced map is a L-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_linear : linear ('ind Hcone : T -> ilT).
Proof.
move=> t u v; apply invlimE => i.
by rewrite !raddfD /= !piindE !linearZ /= piindE.
Qed.
#[export] HB.instance Definition _ :=
  GRing.isLinear.Build R T ilT _ _ (ilind_is_linear).

End UniversalProperty.
End LmodInvLimTheory.


HB.mixin Record isLalgebraInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture lalgType R on Obj*)
  }.
#[short(type="lalgInvLimType")]
HB.structure Definition LalgebraInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of RingInvLim _ Sys ilT
    & LmodInvLim _ Sys ilT
    & isLalgebraInvLim R disp I Obj bonding Sys ilT
    & GRing.Lalgebra R ilT
  }.

Section LAlgInvLimTheory.

Variable (R : ringType).
Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : lalgInvLimType Sys.

(* Rebuild the various instances on a lalgtype. *)
#[export] HB.instance Definition _ i := GRing.Linear.on 'pi[ilT]_i.
(* Check fun i => 'pi[ilT]_i : {lrmorphism ilT -> Obj i}. *)

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism T -> Obj i}).
Hypothesis Hcone : cone Sys f.

(* Rebuild the various instances on a lalgtype. *)
#[export] HB.instance Definition _ i := GRing.Linear.on ('ind[ilT] Hcone).
(* Check 'ind[ilT] Hcone : {lrmorphism T -> ilT}. *)

End UniversalProperty.
End LAlgInvLimTheory.


HB.mixin Record isAlgebraInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
    (ilT : Type) of InvLim disp Sys ilT := {
    (** Capture algType R on Obj*)
  }.
#[short(type="algInvLimType")]
HB.structure Definition AlgebraInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  := {
    ilT of LalgebraInvLim _ Sys ilT
    & isAlgebraInvLim R disp I Obj bonding Sys ilT
    & GRing.Algebra R ilT
  }.

(* What about comAlgType, unitAlgType, comUnitAlgType... ??? *)
(* Not needed unless particular theory need interface    ??? *)


(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)


HB.factory Record InvLim_isNmodInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isNmodInvLim _ _ _ _ Sys ilT.

Implicit Type x y : ilT.

Fact ilzeroP : isthread Sys (fun i => 0 : Obj i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : ilT := ilthr ilzeroP.

Fact iladdP x y : isthread Sys (fun i => 'pi_i x + 'pi_i y).
Proof. by move=> i j Hij; rewrite raddfD (ilprojE x) (ilprojE y). Qed.
Definition iladd x y : ilT := ilthr (iladdP x y).

Fact iladdA : associative iladd.
Proof.  by move=> x y z; apply invlimE=> i; rewrite !ilthrP addrA. Qed.
Fact iladdC : commutative iladd.
Proof. by move=> x y; apply invlimE=> i; rewrite !ilthrP addrC. Qed.
Fact iladd0r : left_id ilzero iladd.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP add0r. Qed.
HB.instance Definition _ :=
    GRing.isNmodule.Build ilT iladdA iladdC iladd0r.

Fact ilproj_is_semi_additive i : semi_additive 'pi[ilT]_i.
Proof. by split=> [|/= x y]; rewrite !ilthrP. Qed.
HB.instance Definition _ :=
  isNmoduleInvLim.Build _ _ _ _ _ ilT ilproj_is_semi_additive.

HB.end.


HB.factory Record InvLim_isZmodInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isZmodInvLim _ _ _ _ Sys ilT.

Implicit Type x y : ilT.

HB.instance Definition _ :=
  InvLim_isNmodInvLim.Build _ _ _ _ Sys ilT.

Fact iloppP x : isthread Sys (fun i => - ('pi_i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : ilT := ilthr (iloppP x).
Fact iladdNr : left_inverse 0 ilopp +%R.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP addNr. Qed.
HB.instance Definition _ :=
  GRing.Nmodule_isZmodule.Build ilT iladdNr.
HB.instance Definition _ :=
  isZmoduleInvLim.Build _ _ _ _ _ ilT.

HB.end.


HB.factory Record InvLim_isSemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isSemiRingInvLim _ _ _ _ Sys ilT.

HB.instance Definition _ :=
  InvLim_isNmodInvLim.Build _ _ _ _ Sys ilT.

Fact iloneP : isthread Sys (fun i => 1 : Obj i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : ilT := ilthr iloneP.

Fact ilmulP x y : isthread Sys (fun i => 'pi[ilT]_i x * 'pi[ilT]_i y).
Proof. by move=> i j Hij; rewrite rmorphM (ilprojE x) (ilprojE y). Qed.
Definition ilmul x y : ilT := ilthr (ilmulP x y).

Fact ilmulA : associative ilmul.
Proof. by move=> x y z; apply invlimE=> i; rewrite !ilthrP mulrA. Qed.
Fact ilmul1r : left_id ilone ilmul.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP mul1r. Qed.
Fact ilmulr1 : right_id ilone ilmul.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP mulr1. Qed.
Fact ilmulDl : left_distributive ilmul +%R.
Proof. by move=> x y z; apply invlimE=> i; rewrite !ilthrP mulrDl. Qed.
Fact ilmulDr : right_distributive ilmul +%R.
Proof. by move=> x y z; apply invlimE=> i; rewrite !ilthrP mulrDr. Qed.
Fact ilmul0r : left_zero 0 ilmul.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP mul0r. Qed.
Fact ilmulr0 : right_zero 0 ilmul.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP mulr0. Qed.
Fact ilone_neq0 : ilone != 0.
Proof.
apply/negP => /eqP/(congr1 (fun x => 'pi_(invsys_inh Sys) x)) /= /eqP.
by rewrite !ilthrP; exact/negP/oner_neq0.
Qed.
HB.instance Definition _ :=
  GRing.Nmodule_isSemiRing.Build ilT
    ilmulA ilmul1r ilmulr1 ilmulDl ilmulDr ilmul0r ilmulr0 ilone_neq0.

Fact ilproj_is_multiplicative i : multiplicative ('pi[ilT]_i).
Proof.
by split => /= [x y|]; rewrite [LHS]ilthrP.
Qed.
HB.instance Definition _ :=
    isSemiRingInvLim.Build _ _ _ _ _ ilT ilproj_is_multiplicative.

HB.end.


HB.factory Record InvLim_isRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isRingInvLim _ _ _ _ Sys ilT.

HB.instance Definition _ :=
  InvLim_isZmodInvLim.Build _ _ _ _ Sys ilT.
HB.instance Definition _ :=
  InvLim_isSemiRingInvLim.Build _ _ _ _ Sys ilT.

HB.end.


HB.factory Record InvLim_isComSemiRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isComSemiRingInvLim _ _ _ _ Sys ilT.

Implicit Type x y : ilT.

HB.instance Definition _ :=
  InvLim_isSemiRingInvLim.Build _ _ _ _ Sys ilT.

Fact ilmulC x y : x * y = y * x.
Proof. by apply invlimE=> i; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ :=
  GRing.SemiRing_hasCommutativeMul.Build ilT ilmulC.
HB.instance Definition _ :=
  isComSemiRingInvLim.Build _ _ _ _ _ ilT.

HB.end.


(** ComRingInvLim is just a join *)


HB.factory Record InvLim_isUnitRingInvLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isUnitRingInvLim _ _ _ _ Sys ilT.

Implicit Type x y : ilT.

HB.instance Definition _ :=
  InvLim_isRingInvLim.Build _ _ _ _ Sys ilT.

Definition ilunit x := `[< forall i, 'pi_i x \is a GRing.unit >].

Fact inv_isunitP x :
  (forall i, 'pi_i x \is a GRing.unit) -> isthread Sys (fun i => ('pi_i x)^-1).
Proof.
by move=> Hunit i j ilej; rewrite /= rmorphV ?(ilprojE x) // Hunit.
Qed.
Definition ilinv x : ilT :=
  if pselect (forall i, 'pi_i x \is a GRing.unit) is left Pf
  then ilthr (inv_isunitP Pf) else x.

Fact ilmulVr : {in ilunit, left_inverse 1 ilinv *%R}.
Proof.
move=> x /asboolP Hinv; apply invlimE=> i.
rewrite /ilinv; case: pselect => /= [H |/(_ Hinv)//].
by rewrite rmorphM rmorph1 /= !ilthrP mulVr.
Qed.
Fact ilmulrV : {in ilunit, right_inverse 1 ilinv *%R}.
Proof.
move=> x /asboolP Hinv; apply invlimE=> i.
rewrite /ilinv; case: pselect => /= [H |/(_ Hinv)//].
by rewrite rmorphM rmorph1 /= !ilthrP mulrV.
Qed.
Fact ilunit_impl x y : y * x = 1 /\ x * y = 1 -> ilunit x.
Proof.
move=> [Hxy Hyx]; apply/asboolP => i; apply/unitrP; exists ('pi_i y).
by split; rewrite -[X in X = 1]rmorphM /= ?Hxy ?Hyx rmorph1.
Qed.
Fact ilinv0id : {in [predC ilunit], ilinv =1 id}.
Proof.
move=> x; rewrite inE /= => /asboolP Hx.
by rewrite /ilinv; case: pselect => /= [/= H|//]; have:= Hx H.
Qed.
HB.instance Definition _ :=
  GRing.Ring_hasMulInverse.Build ilT ilmulVr ilmulrV ilunit_impl ilinv0id.
HB.instance Definition _ :=
  isUnitRingInvLim.Build _ _ _ _ _ ilT.

HB.end.


(** ComUnitRingInvLim is just a join *)


HB.factory Record InvLim_isIDomainInvLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isIDomainInvLim _ _ _ _ Sys ilT.

Implicit Type x y : ilT.

HB.instance Definition _ :=
  InvLim_isUnitRingInvLim.Build _ _ _ _ Sys ilT.
HB.instance Definition _ :=
  InvLim_isComSemiRingInvLim.Build _ _ _ _ Sys ilT.

Fact ilmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> H; case: (altP (x =P 0)) => //= /il_neq0 [i Hi].
move: H; apply contra_eqT => /il_neq0 [j Hj].
have [k ilek jlek] := directedP i j.
have {Hi} /negbTE Hx : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding _ _ ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
have {Hj} /negbTE Hy : 'pi_k y != 0.
  move: Hj; apply contra => /eqP/(congr1 (bonding _ _ jlek)).
  by rewrite (ilprojE y) raddf0 => ->.
apply/negP => /eqP/(congr1 'pi_k)/eqP.
by rewrite rmorph0 rmorphM mulf_eq0 Hx Hy.
Qed.
HB.instance Definition _ :=
  GRing.ComUnitRing_isIntegral.Build ilT ilmul_eq0.
HB.instance Definition _ :=
  isIDomainInvLim.Build _ _ _ _ _ ilT.

HB.end.


HB.factory Record InvLim_isFieldInvLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isFieldInvLim _ _ _ _ Sys ilT.

HB.instance Definition _ :=
  InvLim_isIDomainInvLim.Build _ _ _ _ Sys ilT.

Fact invlim_field_axiom : GRing.field_axiom ilT.
Proof.
move=> x /il_neq0 [i Hi].
apply/asboolP => j; rewrite unitfE.
have [k ilek jlek] := directedP i j.
have {Hi} : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding _ _ ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
by rewrite -(ilprojE x jlek) fmorph_eq0.
Qed.
HB.instance Definition _ :=
    GRing.UnitRing_isField.Build ilT invlim_field_axiom.
HB.instance Definition _ :=
  isFieldInvLim.Build _ _ _ _ _ ilT.

HB.end.


HB.factory Record InvLim_isLmoduleInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isLmoduleInvLim R _ _ _ _ Sys ilT.

Implicit Type (x y : ilT) (r : R).

HB.instance Definition _ :=
  InvLim_isZmodInvLim.Build _ _ _ _ Sys ilT.

Fact ilscaleP r x : isthread Sys (fun i => r *: 'pi[ilT]_i x).
Proof. by move=> i j Hij; rewrite linearZ (ilprojE x). Qed.
Definition ilscale r x : ilT := ilthr (ilscaleP r x).

Fact ilscaleA a b v : ilscale a (ilscale b v) = ilscale (a * b) v.
Proof. by apply invlimE=> i /=; rewrite !ilthrP scalerA. Qed.
Fact ilscale1 : left_id 1 ilscale.
Proof. by move=> x; apply invlimE=> i; rewrite !ilthrP scale1r. Qed.
Fact ilscaleDr : right_distributive ilscale +%R.
Proof.
move=> r x y; apply invlimE=> i.
rewrite raddfD ilthrP raddfD scalerDr /=.
by rewrite [X in _ = X + _]ilthrP [X in _ = _ + X]ilthrP /=.
Qed.
Fact ilscaleDl v : {morph ilscale^~ v: a b / a + b}.
Proof.
by move=> r s; apply invlimE=> i; rewrite !ilthrP scalerDl.
Qed.
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R ilT ilscaleA ilscale1 ilscaleDr ilscaleDl.

Fact ilproj_is_linear i : linear 'pi[ilT]_i.
Proof.
by move=> /= r u v /=; rewrite -!/('pi_i) raddfD /= ilthrP.
Qed.
HB.instance Definition _ :=
  isLmodInvLim.Build R _ _ _ _ _ ilT ilproj_is_linear.

HB.end.


HB.factory Record InvLim_isLalgInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isLalgInvLim R _ _ _ _ Sys ilT.

Implicit Type (x y : ilT) (r : R).

HB.instance Definition _ :=
  InvLim_isRingInvLim.Build _ _ _ _ Sys ilT.
HB.instance Definition _ :=
  InvLim_isLmoduleInvLim.Build R _ _ _ _ Sys ilT.

Fact ilscaleAl r x y : r *: (x * y) = r *: x * y.
Proof.
by apply invlimE=> i /=; rewrite ilthrP !rmorphM /= ilthrP scalerAl.
Qed.
HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R ilT ilscaleAl.
HB.instance Definition _ :=
  isLalgebraInvLim.Build R _ _ _ _ Sys ilT.

HB.end.


HB.factory Record InvLim_isAlgebraInvLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim _ Sys ilT := {}.
HB.builders Context
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : is_invsys bonding)
  ilT of InvLim_isAlgebraInvLim R _ _ _ _ Sys ilT.

Implicit Type (x y : ilT) (r : R).

HB.instance Definition _ :=
  InvLim_isLalgInvLim.Build R _ _ _ _ Sys ilT.

Fact ilscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof.
by apply invlimE=> i /=; rewrite !(linearZ, rmorphM) /= linearZ /= !scalerAr.
Qed.
HB.instance Definition _ :=
  GRing.Lalgebra_isAlgebra.Build R ilT ilscaleAr.
HB.instance Definition _ :=
  isAlgebraInvLim.Build R _ _ _ _ _ ilT.

HB.end.


Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for inverse limits                            *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.

Record invlim := MkInvLim {
                     invlimthr :> forall i, Obj i;
                     _ : `[< isthread Sys invlimthr >];
                   }.

(** A non canonical subtype for invlim *)
Definition invlim_subType : subType _ :=
  HB.pack invlim [isSub for invlimthr].
HB.instance Definition _ := gen_eqMixin invlim.
HB.instance Definition _ := gen_choiceMixin invlim.

End Implem.
Notation "{ 'invlim' S }" := (invlim S).


Section InverseLimitTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.

Implicit Type (i j k : I) (x y : {invlim Sys}).

Definition ilproj_impl i : {invlim Sys} -> Obj i :=
  (invlimthr (Sys := Sys))^~ i.

Lemma ilproj_implE x :
  forall i j, forall (Hij : i <= j),
      bonding Hij (ilproj_impl j x) = ilproj_impl i x.
Proof. by case: x => [thr /asboolP] /=. Qed.

Local Notation "''pi_' i" := (ilproj_impl i).

Lemma invlimP x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> eqxy; apply (val_inj (sT := invlim_subType _)) => /=.
case: x y eqxy => [fx _] [fy _] /=.
exact: functional_extensionality_dep.
Qed.

(** Building the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, T -> Obj i).
Hypothesis Hcone : cone Sys f.

Definition ilind_impl t := MkInvLim (asboolT (cone_thr Hcone t)).

Lemma ilind_implP i t : 'pi_i (ilind_impl t) = f i t.
Proof. by []. Qed.

Lemma ilind_implE (un : T -> {invlim Sys}) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 ilind_impl.
Proof.
move=> H x; apply invlimP => i.
by rewrite -/(('pi_i \o un) _) H ilind_implP.
Qed.

End UniversalProperty.

Lemma ilimpl_projP : cone Sys ilproj_impl.
Proof. by move=> i j Hij x; apply: ilproj_implE. Qed.

HB.instance Definition _ :=
  isInvLim.Build _ _ _ _ Sys {invlim Sys} ilimpl_projP ilind_implP ilind_implE.

End InverseLimitTheory.

Open Scope ring_scope.

Section Instances.

Variables (disp : unit) (I : porderType disp).

Section Nmodule.
Variable Obj : I -> nmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := InvLim_isNmodInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Nmodule.

Section Zmodule.
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := InvLim_isZmodInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Zmodule.

Section SemiRing.
Variable Obj : I -> semiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isSemiRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End SemiRing.

Section Ring.
Variable Obj : I -> ringType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := InvLim_isRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Ring.

Section ComSemiRing.
Variable Obj : I -> comSemiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isComSemiRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End ComSemiRing.

Section ComRing.
Variable Obj : I -> comRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := InvLim.on {invlim Sys}.
Let test : comRingInvLimType _ := {invlim Sys}.
End ComRing.

Section UnitRing.
Variable Obj : I -> unitRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isUnitRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End UnitRing.

Section ComUnitRing.
Variable Obj : I -> comUnitRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := InvLim.on {invlim Sys}.
Let test : comUnitRingInvLimType _ := {invlim Sys}.
End ComUnitRing.

Section Linear.
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isLmoduleInvLim.Build R _ _ _ _ Sys {invlim Sys}.
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isLalgInvLim.Build R _ _ _ _ Sys {invlim Sys}.
End Lalg.

Section Alg.
Variables (R : ringType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isAlgebraInvLim.Build R _ _ _ _ Sys {invlim Sys}.
Let test : algInvLimType _ := {invlim Sys}.
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Obj : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := GRing.Algebra.on {invlim Sys}.
End UnitAlg.

Section ComAlg.
Variables (R : comRingType).
Variable Obj : I -> comAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := GRing.Algebra.on {invlim Sys}.
End ComAlg.

Section ComUnitAlg.
Variables (R : comUnitRingType).
Variable Obj : I -> comAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ := GRing.Algebra.on {invlim Sys}.
End ComUnitAlg.

End Instances.

Section IDomain.
Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> idomainType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isIDomainInvLim.Build _ _ _ _ Sys {invlim Sys}.
Let test : idomainInvLimType _ := {invlim Sys}.
End IDomain.

Section Field.
Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> fieldType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
HB.instance Definition _ :=
  InvLim_isFieldInvLim.Build _ _ _ _ Sys {invlim Sys}.
Let test : fieldInvLimType _ := {invlim Sys}.
End Field.


Section TestComUnitAlg.
Variables (R : ringType).
Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> comUnitAlgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Let test1 : algInvLimType _ := {invlim Sys}.
Let test2 : comUnitRingInvLimType _ := {invlim Sys}.
End TestComUnitAlg.


(***************************************************************************)
(** Valuation in inverse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Obj : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%N -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : zmodInvLimType Sys.
Implicit Types (i n : nat) (x y : ilT).

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

Lemma ltn_valuatP x n : reflect ('pi_n x = 0) (Nat n < valuat x).
Proof.
apply (iffP idP); case: valuatP => [v Hv vmin /= |->].
- by rewrite ltEnatbar; apply vmin.
- by rewrite raddf0.
- apply contra_eqT; rewrite ltEnatbar -leqNgt => vleq.
  apply/contra: Hv => /eqP/(congr1 (bonding vleq)).
  by rewrite (ilprojE x) raddf0 => ->.
- by [].
Qed.

Lemma leq_valuatP x n :
  reflect (forall i, (i < n)%N -> 'pi_i x = 0) (Nat n <= valuat x).
Proof.
apply (iffP idP).
- case: valuatP => [v Hv vmin /= |-> _ i _].
  + by rewrite leEnatbar => nlev i /leq_trans/(_ nlev); apply vmin.
  + by rewrite raddf0.
- case: n => // n; first exact: le0bar.
  move=> /(_ n)/(_ (ltnSn _)) /ltn_valuatP.
  by case: (valuat x)=> // v; rewrite ltEnatbar leEnatbar.
Qed.

Lemma proj_gt_valuat x n : (Nat n >= valuat x) = ('pi_n x != 0).
Proof. by apply negb_inj; rewrite negbK -ltNge; apply/ltn_valuatP/eqP. Qed.

Lemma valuatNatE x n :
  'pi_n x != 0 -> (forall i, (i < n)%N -> 'pi_i x = 0) -> valuat x = Nat n.
Proof.
move=> Hn nmin; apply le_anti; rewrite proj_gt_valuat Hn /=.
exact/leq_valuatP.
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite raddf0 eqxx. Qed.

Lemma valuat0P x : (valuat x == Inf) = (x == 0).
Proof.
apply/eqP/eqP=> [valx|->]; last exact: valuat0.
by apply/invlimE=> i; rewrite raddf0; apply/ltn_valuatP; rewrite valx.
Qed.

Lemma le_valuatP x y :
  reflect (forall i, 'pi_i x = 0 -> 'pi_i y = 0) (valuat x <= valuat y).
Proof.
case Hvx: (valuat x) => [vx|].
- apply (iffP (leq_valuatP _ _)) => Hv i Hx; apply: Hv.
  + by move/ltn_valuatP: Hx; rewrite Hvx ltEnatbar.
  + by apply/ltn_valuatP; rewrite Hvx ltEnatbar.
- rewrite le1x valuat0P; apply (iffP idP) => [/eqP -> i _| H].
    by rewrite raddf0.
  apply/eqP/invlimE => /= i; rewrite raddf0; apply H.
  by move/eqP: Hvx => /[!valuat0P] /eqP -> /[!raddf0].
Qed.

Lemma eq_valuatP x y :
  reflect (forall i, 'pi_i x = 0 <-> 'pi_i y = 0) (valuat x == valuat y).
Proof.
rewrite eq_le; apply (iffP andP) => [[/le_valuatP vxy /le_valuatP vyx i] | H].
  split; [exact: vxy | exact: vyx].
by split; apply/le_valuatP => i; rewrite H.
Qed.

Lemma valuatN x : valuat (- x) = valuat x.
Proof.
apply/eqP/eq_valuatP => i.
rewrite raddfN /= -{1}oppr0; split=> [/eqP |-> //].
by rewrite eqr_opp => /eqP.
Qed.

Lemma valuatD x1 x2 :
  Order.min (valuat x1) (valuat x2) <= valuat (x1 + x2).
Proof.
wlog v1lev2 : x1 x2 / valuat x1 <= valuat x2.
  move=> Hlog; case (leP (valuat x1) (valuat x2)) => [|/ltW]/Hlog //.
  by rewrite addrC minC.
rewrite (min_idPl v1lev2); move: v1lev2.
move/le_valuatP => H12; apply/le_valuatP => i /[dup]/H12 p10 p20.
by rewrite raddfD /= p10 p20 addr0.
Qed.

Lemma valuat_sum I r P (F : I ->  ilT) :
  \meet_(i <- r | P i) valuat (F i) <= valuat (\sum_(i <- r | P i) F i).
Proof.
apply: (big_ind2 (fun x v => v <= valuat x)); rewrite ?valuat0 //=.
by move=> x1 v1 x2 v2 H1 H2; apply: (le_trans (leI2 _ _) (valuatD x1 x2)).
Qed.

Lemma valuatB s1 s2 :
  Order.min (valuat s1) (valuat s2) <= valuat (s1 - s2).
Proof. by have:= valuatD s1 (-s2); rewrite valuatN. Qed.

Lemma valuatDr s1 s2 :
  valuat s1 < valuat s2 -> valuat (s1 + s2) = valuat s1.
Proof.
case: (valuatP s2) => [v2 _   v2min|-> _]; last by rewrite addr0.
case: (valuatP s1) => [v1 Hv1 v1min|->]; last by rewrite ltIbar.
rewrite ltEnatbar => v12.
apply valuatNatE=> [|n nv1]; rewrite raddfD /= v2min ?addr0 // ?v1min //.
exact: ltn_trans nv1 v12.
Qed.
Lemma valuatDl s1 s2 :
  valuat s1 < valuat s2 -> valuat (s2 + s1) = valuat s1.
Proof. by rewrite addrC; apply valuatDr. Qed.

Lemma valuatBr s1 s2 :
  valuat s1 < valuat s2 -> valuat (s1 - s2) = valuat s1.
Proof. by rewrite -(valuatN s2) => /valuatDr. Qed.
Lemma valuatBl s1 s2 :
  valuat s2 < valuat s1 -> valuat (s1 - s2) = valuat s2.
Proof. by rewrite -(valuatN s2) addrC => /valuatDr. Qed.

End Valuation.


Section ValuationLmodOverRing.

Variable R : ringType.
Variable Obj : nat -> lmodType R.
Variable bonding : forall i j : nat, (i <= j)%N -> {linear Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : lmodInvLimType Sys.
Implicit Types (r : R) (x y : ilT).

Lemma valuat_scale r x : valuat x <= valuat (r *: x).
Proof. by apply/le_valuatP => i /[!linearZ] /= -> /[!scaler0]. Qed.

End ValuationLmodOverRing.


Section ValuationLmodOverUnitRing.

Variable R : unitRingType.
Variable Obj : nat -> lmodType R.
Variable bonding : forall i j : nat, (i <= j)%N -> {linear Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : lmodInvLimType Sys.
Implicit Types (r : R) (x y : ilT).

Lemma valuat_scale_unit r x :
  r \is a GRing.unit -> valuat (r *: x) = valuat x.
Proof.
move=> runit; apply le_anti; rewrite valuat_scale /=.
by rewrite -{2}(scale1r x) -(mulVr runit) -scalerA valuat_scale.
Qed.

End ValuationLmodOverUnitRing.


Section ValuationRing.

Variable Obj : nat -> ringType.
Variable bonding : forall i j : nat, (i <= j)%N -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : ringInvLimType Sys.
Implicit Type (x y : ilT).

Lemma valuat1 : valuat (1 : ilT) = Nat 0.
Proof. by apply valuatNatE => [|i //]; rewrite rmorph1 oner_neq0. Qed.

Lemma valuatMl x1 x2 : valuat x1 <= valuat (x1 * x2).
Proof. by apply/le_valuatP => i /[!rmorphM] /= ->; rewrite mul0r. Qed.
Lemma valuatMr x1 x2 : valuat x2 <= valuat (x1 * x2).
Proof.
Proof. by apply/le_valuatP => i /[!rmorphM] /= ->; rewrite mulr0. Qed.

Lemma valuatM x1 x2 : Order.max (valuat x1) (valuat x2) <= valuat (x1 * x2).
Proof. by rewrite leUx valuatMl valuatMr. Qed.

Lemma valuat_prod I r P (F : I ->  ilT) :
  \join_(i <- r | P i) valuat (F i) <= valuat (\prod_(i <- r | P i) F i).
Proof.
apply: (big_ind2 (fun x v => v <= valuat x)); rewrite ?valuat1 //=.
by move=> x1 v1 x2 v2 H1 H2; apply: (le_trans (leU2 _ _) (valuatM x1 x2)).
Qed.

End ValuationRing.


(** Only need join RingInvLim & UnitRing *)
Section ValuationUnitRing.

Variable Obj : nat -> ringType.
Variable bonding : forall i j : nat, (i <= j)%N -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.

Variable ilT : Unit_RingInvLimType Sys.
Implicit Type (x y : ilT).

Lemma valuatV x : x \is a GRing.unit -> valuat x = Nat 0.
Proof.
move=> xunit; apply/eqP; rewrite -lex0 /=.
have <- : valuat (x * x^-1) = \bot by rewrite divrr // valuat1.
exact: valuatMl.
Qed.

Lemma valuatVM x y : x \is a GRing.unit -> valuat (x * y) = valuat y.
Proof.
move=> xunit; apply/eqP; rewrite eq_le valuatMr andbT.
by rewrite -{2}(mulKr xunit y) valuatMr.
Qed.

Lemma valuatMV x y : x \is a GRing.unit -> valuat (y * x) = valuat y.
Proof.
move=> xunit; apply/eqP; rewrite eq_le valuatMl andbT.
by rewrite -{2}(mulrK xunit y) valuatMl.
Qed.

End ValuationUnitRing.


Section CommHugeOp.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j : I, i <= j -> Obj j -> Obj i.
Variable Sys : is_invsys bonding.
Variable ilT : invLimType Sys.

Variable (C : choiceType).
Variables (idx : ilT) (op : Monoid.com_law idx).

Implicit Type F : C -> ilT.
Implicit Types (x y z t : ilT).

Definition invar i x := forall s, 'pi_i (op x s) = 'pi_i s.
Definition is_ilopable F :=
  `[< forall i, exists S : {fset C}, forall c, c \notin S -> invar i (F c)>].
Lemma ilopand_spec F :
  is_ilopable F ->
  forall i, { f : {fset C} | f =i predC (fun c => `[< invar i (F c)>]) }.
Proof.
move=> H i; move/asboolP/(_ i): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq c <- s | ~~ `[< invar i (F c)>]]) => c.
rewrite seq_fsetE !inE mem_filter.
by case: (boolP `[< _>]) => //=; apply contraR => /Hs/asboolT.
Qed.
Definition ilopand F (sm : is_ilopable F) c :=
  let: exist fs _ := ilopand_spec sm c in fs.

Lemma ilopandP F (sm : is_ilopable F) i c :
  reflect (invar i (F c)) (c \notin (ilopand sm i)).
Proof.
rewrite /ilopand; apply (iffP negP); case: ilopand_spec => f Hf.
- by rewrite Hf inE => /negP; rewrite negbK => /asboolW.
- by rewrite Hf inE => H; apply/negP; rewrite negbK; apply asboolT.
Qed.

Lemma ilopand_subset F (sm : is_ilopable F) i j :
  i <= j -> (ilopand sm i `<=` ilopand sm j)%fset.
Proof.
move=> ilej.
apply/fsubsetP => c; apply/contraLR => /ilopandP Hinv.
by apply/ilopandP => x; rewrite -!(ilprojE _ ilej) Hinv.
Qed.

Fact ilopand_istrhead F (sm : is_ilopable F) :
  isthread Sys (fun i => 'pi_i (\big[op/idx]_(c <- ilopand sm i) F c)).
Proof.
move=> i j Hij; rewrite ilprojE.
rewrite (bigID (fun c => `[< invar i (F c)>])) /=.
set X := (X in op _ X); set Y := (Y in _ = _ Y).
have {X} -> : X = Y.
  rewrite {}/X {}/Y; apply eq_fbigl_cond => c.
  rewrite !inE andbT; apply negb_inj; rewrite negb_and negbK.
  case: (boolP (c \in (ilopand sm j))) => /= Hc.
  - by apply/asboolP/idP=> /ilopandP //; apply.
  - suff -> : c \notin (ilopand sm i) by [].
    by apply/contra: Hc; apply: (fsubsetP (ilopand_subset sm Hij)).
elim: (X in \big[op/idx]_(i <- X | _) _) => [| s0 s IHs].
  by rewrite big_nil Monoid.mul1m.
rewrite big_cons /=; case: asboolP => [|]; last by rewrite IHs.
by rewrite -Monoid.mulmA {1}/invar => ->.
Qed.

Definition HugeOp F : ilT :=
  if pselect (is_ilopable F) is left sm
  then ilthr (ilopand_istrhead sm)
  else idx.

Local Notation "\Op_( c ) F" := (HugeOp (fun c => F)) (at level 0).

Lemma projHugeOp F i (S : {fset C}) :
  is_ilopable F ->
  subpred (predC (mem S)) (fun c => `[< invar i (F c)>]) ->
  'pi_i (\Op_(c) (F c)) = 'pi_i (\big[op/idx]_(c <- S) F c).
Proof.
rewrite /HugeOp=> Hop Hsub; case: pselect => [/= {}Hop |/(_ Hop) //].
transitivity ('pi_i (\big[op/idx]_(c <- S | c \in ilopand Hop i) F c));
    first last.
  rewrite [in RHS](bigID [pred c | `[< invar i (F c)>]]) /=.
  set Inv := (X in op X _); have {Inv} -> : invar i Inv.
    rewrite {}/Inv; elim: {1}(enum_fset S) => [| s0 s IHs].
      by rewrite  big_nil => s; rewrite Monoid.mul1m.
    rewrite big_cons.
    by case asboolP; rewrite {1}/invar => H s1 //; rewrite -Monoid.mulmA H IHs.
  congr 'pi_i; apply: eq_big => x //.
  by apply/negb_inj; rewrite negbK; apply/ilopandP/asboolP.
rewrite ilthrP; congr 'pi_i.
rewrite [in RHS]big_fset_condE; apply: eq_fbigl => c.
rewrite !inE andbC.
case: (boolP (c \in _)) => //= /ilopandP/asboolP Hc; apply/esym.
by have /contraR /= := Hsub c; rewrite -asbool_neg => /(_ Hc).
Qed.

End CommHugeOp.


Section Summable.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : zmodInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> ilT.
Implicit Types (s x y z t : ilT).

Let add_law : Monoid.com_law 0 := (+%R : ilT -> ilT -> ilT).

Definition is_summable F := is_ilopable add_law F.
Definition summand F (sm : is_summable F) := ilopand sm.
Definition HugeSum F : ilT := HugeOp add_law F.

Local Notation "\Sum_( c ) F" := (HugeSum (fun c => F)).

Lemma invar_addE F i c : invar add_law i (F c) <-> 'pi_i (F c) = 0.
Proof.
rewrite /invar /=; split => [/(_ 0)| H0 x]; first by rewrite addr0 raddf0.
by rewrite raddfD /= H0 add0r.
Qed.

Lemma is_summableP F :
  (is_summable F) <->
  (forall i, exists S : {fset C}, forall c, c \notin S -> 'pi_i (F c) = 0).
Proof.
split.
- rewrite /is_summable/is_ilopable => /asboolP H i.
  move: H => /(_ i) [S HS]; exists S => c /HS.
  by rewrite invar_addE.
- move=> H; apply/asboolP => i; move/(_ i): H => [S Hs].
  by exists S => c; rewrite invar_addE => /Hs.
Qed.

Lemma summandP F (sm : is_summable F) i c :
  reflect ('pi_i (F c) = 0) (c \notin (summand sm i)).
Proof. by apply (iffP (ilopandP _ _ _)); rewrite invar_addE. Qed.

Lemma summand_subset F (sm : is_summable F) i j :
  i <= j -> (summand sm i `<=` summand sm j)%fset.
Proof. exact: ilopand_subset. Qed.

Lemma projHugeSum F i (S : {fset C}) :
  is_summable F ->
  (forall c : C, c \notin S -> 'pi_i (F c) = 0) ->
  'pi_i (\Sum_(c) F c) = 'pi_i (\sum_(c <- S) F c).
Proof.
move=> /projHugeOp H Hpred; apply: H => c {}/Hpred /= H.
by apply/asboolP; rewrite invar_addE.
Qed.

End Summable.



Section Prodable.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> comRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : is_invsys bonding.
Variable ilT : comRingInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> ilT.
Implicit Types (s x y z t : ilT).

Let mul_law : Monoid.com_law 1 := ( *%R : ilT -> ilT -> ilT).

Definition is_prodable F := is_ilopable mul_law F.
Definition prodand F (sm : is_prodable F) := ilopand sm.
Definition HugeProd F : ilT := HugeOp mul_law F.

Local Notation "\Prod_( c ) F" := (HugeProd (fun c => F)) (at level 0).

Lemma invar_mulE F i c : invar mul_law i (F c) <-> 'pi_i (F c) = 1.
Proof.
rewrite /invar /=; split => [/(_ 1)| H0 x].
  by rewrite rmorphM /= rmorph1 mulr1.
by rewrite rmorphM /= H0 mul1r.
Qed.

Lemma is_prodableP F :
  (is_prodable F) <->
  (forall i, exists S : {fset C}, forall c, c \notin S -> 'pi_i (F c) = 1).
Proof.
split.
- rewrite /is_prodable/is_ilopable => /asboolP H i.
  move: H => /(_ i) [S HS]; exists S => c /HS.
  by rewrite invar_mulE.
- move=> H; apply/asboolP => i; move/(_ i): H => [S Hs].
  by exists S => c; rewrite invar_mulE => /Hs.
Qed.

Lemma prodandP F (sm : is_prodable F) i c :
  reflect ('pi_i (F c) = 1) (c \notin (prodand sm i)).
Proof. by apply (iffP (ilopandP _ _ _)); rewrite invar_mulE. Qed.

Lemma prodand_subset F (sm : is_prodable F) i j :
  i <= j -> (prodand sm i `<=` prodand sm j)%fset.
Proof. exact: ilopand_subset. Qed.

Lemma projHugeProd F i (S : {fset C}) :
  is_prodable F ->
  (forall c : C, c \notin S -> 'pi_i (F c) = 1) ->
  'pi_i (\Prod_( c ) (F c)) = 'pi_i (\prod_(c <- S) F c).
Proof.
move=> /projHugeOp H Hpred; apply: H => c {}/Hpred /= H.
by apply/asboolP; rewrite invar_mulE.
Qed.

End Prodable.
