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
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order finmap bigop.

Require Import natbar directed.


Import GRing.
Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'invlim' S }"
         (at level 0, format "{ 'invlim'  S }").
Reserved Notation "''pi_' i" (at level 8, i at level 2, format "''pi_' i").

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

Variables (disp : Datatypes.unit) (I : porderType disp).

(** Objects and bonding morphisms of the inverse system at left outside    *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Obj : I -> Type.
Variable bonding : (forall i j, i <= j -> Obj j -> Obj i).
Record invsys : Type := InvSys {
      invsys_inh : I;
      invsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      invsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hij) \o (bonding Hjk) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition isthread of invsys := fun thr : forall i, Obj i =>
  forall i j, forall (Hij : i <= j), bonding Hij (thr j) = thr i.

Definition cone of invsys := fun T (mors : forall i, T -> Obj i) =>
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

#[key="TLim"]
HB.mixin Record isInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj j -> Obj i)
    (Sys : invsys bonding)
  TLim of Choice TLim := {
    invlim_proj : forall i, TLim -> Obj i;
    invlim_ind  : forall (T : Type) (f : forall i, T -> Obj i),
      (cone Sys f) -> T -> TLim;
    ilprojP : cone Sys invlim_proj;
    ilind_commute : forall T (f : forall i, T -> Obj i) (Hcone : cone Sys f),
      forall i, invlim_proj i \o invlim_ind _ _ Hcone =1 f i;
    ilind_uniq : forall T (f : forall i, T -> Obj i) (Hcone : cone Sys f),
      forall (ind : T -> TLim),
        (forall i, invlim_proj i \o ind =1 f i) ->
        ind =1 invlim_ind _ _ Hcone
  }.

#[short(type="invLimType")]
HB.structure Definition InvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj j -> Obj i)
    (Sys : invsys bonding)
  := {
    TLim of isInvLim disp I Obj bonding Sys TLim
    & Choice TLim
  }.



Section InternalTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : invsys bonding.
Variable ilT : invLimType Sys.

Definition pi_phant of phant ilT := (@invlim_proj _ _ _ _ _ ilT).
Local Notation "\pi" := (pi_phant (Phant ilT)).
Definition ind_phant of phant ilT := (@invlim_ind _ _ _ _ _ ilT).
Local Notation "\ind" := (ind_phant (Phant ilT)).

Lemma ilprojE (x : ilT) :
  forall i j, forall (Hij : i <= j), bonding Hij (\pi j x) = \pi i x.
Proof.
move=> i j Hij.
by rewrite -/((bonding Hij \o (pi_phant (Phant ilT)) j) x) ilprojP.
Qed.

Lemma piindE  T (f : forall i, T -> Obj i) (Hcone : cone Sys f) i x :
  \pi i (\ind Hcone x) = f i x.
Proof. exact: ilind_commute. Qed.

End InternalTheory.

Arguments ilprojP {disp I Obj bonding} [Sys].

Notation "''pi_' i" := (pi_phant (Phant _) i).
Notation "''pi[' T ']_' i" := (pi_phant (Phant T) i)
                              (at level 8, i at level 2, only parsing).
Notation "''ind'" := (ind_phant (Phant _)).
Notation "''ind[' T ']'" := (ind_phant (Phant T)) (only parsing).


Section Theory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : invsys bonding.
Variable ilT : invLimType Sys.

Lemma invlimE (x y : ilT) : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq.
pose fx : forall i : I, Datatypes.unit -> Obj i := fun i tt => 'pi_i x.
have compf : cone Sys fx.
  by rewrite /fx => i j le_ij tt /=; rewrite ilprojE.
pose ind z : Datatypes.unit -> ilT := fun tt => z.
have Huniqy i : 'pi_i \o ind y =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
have Huniqx i : 'pi_i \o ind x =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
move: (ilind_uniq _ _ compf _ Huniqx tt) (ilind_uniq _ _ compf _ Huniqy tt).
by rewrite /ind => -> ->.
Qed.

Lemma from_thread_spec (thr : forall i : I, Obj i) :
  isthread Sys thr -> { t : ilT | forall i, 'pi_i t = thr i }.
Proof.
rewrite /isthread => Hhtr.
pose f : forall i : I, Datatypes.unit -> Obj i := fun i tt => thr i.
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

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : invsys bonding.
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

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> eqType.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.

Variable Sys : invsys bonding.
Variable T : invLimType Sys.
Implicit Type x y : T.

Lemma invlimPn x y : reflect (exists i, 'pi_i x != 'pi_i y) (x != y).
Proof.
apply (iffP idP) => [neq|[i]]; last by apply/contra => /eqP ->.
apply/asboolP; rewrite asbool_existsNb; apply/contra: neq => /asboolP Hx.
by apply/eqP/invlimE => /= i; apply/eqP.
Qed.

End InvLimitEqType.




(****************************************************************************)
(**  Interface for inverse limits in various algebraic categories           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)
Open Scope ring_scope.


#[key="TLim"]
HB.mixin Record isZmoduleInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : invsys bonding)
    (TLim : Type) of InvLim disp Sys TLim & Zmodule TLim := {
  ilproj_is_additive :
    forall i, additive ('pi[TLim]_i)
  }.

#[short(type="zmodInvLimType")]
HB.structure Definition ZmodInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of InvLim disp Sys TLim
    & isZmoduleInvLim disp I Obj bonding Sys TLim
    & Zmodule TLim
  }.

About InvLim.

Section ZmodInvLimTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : zmodInvLimType Sys.
Implicit Type x y : TLim.

HB.instance Definition _ i :=
  isAdditive.Build TLim (Obj i) _ (ilproj_is_additive i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_additive : additive ('ind[TLim] Hcone).
Proof.
by move=> t u; apply invlimE=> j; rewrite raddfB /= !piindE raddfB.
Qed.
HB.instance Definition _ :=
  isAdditive.Build T TLim _ ilind_is_additive.

End UniversalProperty.

Lemma il_neq0 x : x != 0 -> exists i, 'pi_i x != 0.
Proof. by move/invlimPn=> [i]; rewrite raddf0 => Hi; exists i. Qed.

End ZmodInvLimTheory.


#[key="TLim"]
HB.mixin Record isRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
    (TLim : Type) of InvLim disp Sys TLim & Ring TLim := {
  ilproj_is_multiplicative :
    forall i, multiplicative ('pi[TLim]_i)
  }.

#[short(type="ringInvLimType")]
HB.structure Definition RingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of ZmodInvLim disp Sys TLim
    & isRingInvLim disp I Obj bonding Sys TLim
    & Ring TLim
  }.

Section RingInvLimTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> ringType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type x y : TLim.

HB.instance Definition _ i :=
  isMultiplicative.Build TLim (Obj i) _ (ilproj_is_multiplicative i).

Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_multiplicative : multiplicative ('ind[TLim] Hcone).
Proof.
by split => [/= t u|]; apply invlimE=> i;
  rewrite !piindE ?rmorph1 ?rmorphM //= !piindE.
Qed.
HB.instance Definition _ :=
  isMultiplicative.Build T TLim _ ilind_is_multiplicative.

End UniversalProperty.

Lemma il_neq1 x : x != 1 -> exists i, 'pi_i x != 1.
Proof. by move/invlimPn=> [i]; rewrite rmorph1 => Hi; exists i. Qed.

End RingInvLimTheory.


#[short(type="comRingInvLimType")]
HB.structure Definition ComRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of ComRing TLim
    & RingInvLim disp Sys TLim
  }.

#[short(type="unitRingInvLimType")]
HB.structure Definition UnitRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of UnitRing TLim
    & RingInvLim disp Sys TLim
  }.

Section InvLimUnitRingTheory.

Variables
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding).
Variable TLim : unitRingInvLimType Sys.

Lemma ilunitP (x : TLim) :
  reflect (forall i, 'pi_i x \is a unit) (x \is a unit).
Proof.
apply (iffP idP) => [xunit i | H]; first exact: rmorph_unit.
have invthr : isthread Sys (fun i => ('pi_i x)^-1).
  by move=> i j ilej; rewrite /= rmorphV ?(ilprojE x) // H.
apply/unitrP; exists (ilthr invthr).
split; apply: invlimE => i; rewrite rmorph1 rmorphM /= ilthrP.
- exact: (mulVr (H i)).
- exact: (mulrV (H i)).
Qed.

End  InvLimUnitRingTheory.


#[short(type="comUnitRingInvLimType")]
HB.structure Definition ComUnitRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of ComUnitRing TLim
    & RingInvLim disp Sys TLim
  }.

#[key="TLim"]
  HB.mixin Record isLmodInvLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : invsys bonding)
    (TLim : Type) of InvLim disp Sys TLim & Lmodule R TLim := {
  ilproj_is_linear :
    forall i, linear ('pi[TLim]_i)
  }.

#[short(type="lmodInvLimType")]
HB.structure Definition LmodInvLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of ZmodInvLim _ Sys TLim
    & isLmodInvLim R disp I Obj bonding Sys TLim
    & Lmodule R TLim
  }.


Section LmodInvLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : lmodInvLimType Sys.

HB.instance Definition _ i :=
  isLinear.Build R TLim (Obj i) _ _ (ilproj_is_linear i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear T -> Obj i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_linear : linear ('ind Hcone : T -> TLim).
Proof.
move=> t u v; apply invlimE => i.
by rewrite !raddfD /= !piindE !linearZ /= piindE.
Qed.
HB.instance Definition _ :=
  isLinear.Build R T TLim _ _ (ilind_is_linear).

End UniversalProperty.
End LmodInvLimTheory.


(* TODO: no builder ??? *)
#[short(type="lalgInvLimType")]
HB.structure Definition LalgebraInvLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  := {
    TLim of Lalgebra R TLim
    & RingInvLim _ Sys TLim
    & LmodInvLim _ Sys TLim
  }.


Section LAlgInvLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : lalgInvLimType Sys.

(* Rebuilt the various instances on a lalgtype. *)
HB.instance Definition _ i := Linear.on 'pi[TLim]_i.
(* Check fun i => 'pi[TLim]_i : {lrmorphism TLim -> Obj i}. *)

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism T -> Obj i}).
Hypothesis Hcone : cone Sys f.

(* Rebuild the various instances on a lalgtype. *)
HB.instance Definition _ i := Linear.on ('ind[TLim] Hcone).
(* Check 'ind[TLim] Hcone : {lrmorphism T -> TLim}. *)

End UniversalProperty.
End LAlgInvLimTheory.

(* TODO : What about comRingType, comAlgType, unitRingType, ... ??? *)
(* Not needed unless particular theory need interface           ??? *)



(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)


HB.factory Record InvLim_isZmodInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isZmodInvLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

Fact ilzeroP : isthread Sys (fun i => 0 : Obj i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : TLim := ilthr ilzeroP.

Fact iloppP x : isthread Sys (fun i => - ('pi_i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : TLim := ilthr (iloppP x).

Fact iladdP x y : isthread Sys (fun i => 'pi_i x + 'pi_i y).
Proof. by move=> i j Hij; rewrite raddfD (ilprojE x) (ilprojE y). Qed.
Definition iladd x y : TLim := ilthr (iladdP x y).

Fact iladdA : associative iladd.
Proof.  by move=> a b c; apply invlimE=> i; rewrite !ilthrP addrA. Qed.
Fact iladdC : commutative iladd.
Proof. by move=> a b; apply invlimE=> i; rewrite !ilthrP addrC. Qed.
Fact iladd0r : left_id ilzero iladd.
Proof. by move=> b; apply invlimE=> i; rewrite !ilthrP add0r. Qed.
Fact iladdNr : left_inverse ilzero ilopp iladd.
Proof. by move=> b; apply invlimE=> i; rewrite !ilthrP addNr. Qed.
HB.instance Definition _ :=
    isZmodule.Build TLim iladdA iladdC iladd0r iladdNr.

Fact ilproj_is_additive i : additive 'pi[TLim]_i.
Proof.
move=> /= x y /=.  (* Coq needs help tofind where to rewrite ilthrP *)
by rewrite [LHS]ilthrP [X in _ + X]ilthrP.
Qed.
HB.instance Definition _ :=
  isZmoduleInvLim.Build _ _ _ _ _ TLim ilproj_is_additive.

HB.end.


HB.factory Record InvLim_isRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isRingInvLim _ _ _ _ Sys TLim.

HB.instance Definition _ :=
  InvLim_isZmodInvLim.Build _ _ _ _ Sys TLim.

Fact iloneP : isthread Sys (fun i => 1 : Obj i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : TLim := ilthr iloneP.

Fact ilmulP x y : isthread Sys (fun i => 'pi[TLim]_i x * 'pi[TLim]_i y).
Proof. by move=> i j Hij; rewrite rmorphM (ilprojE x) (ilprojE y). Qed.
Definition ilmul x y : TLim := ilthr (ilmulP x y).

Fact ilmulA : associative ilmul.
Proof. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrA. Qed.
Fact ilmul1r : left_id ilone ilmul.
Proof. by move=> a; apply invlimE=> i; rewrite !ilthrP mul1r. Qed.
Fact ilmulr1 : right_id ilone ilmul.
Proof. by move=> a; apply invlimE=> i; rewrite !ilthrP mulr1. Qed.
Fact ilmulDl : left_distributive ilmul +%R.
Proof. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrDl. Qed.
Fact ilmulDr : right_distributive ilmul +%R.
Proof. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrDr. Qed.
Fact ilone_neq0 : ilone != 0.
Proof.
apply/negP => /eqP/(congr1 (fun x => 'pi_(invsys_inh Sys) x)) /= /eqP.
by rewrite !ilthrP; exact/negP/oner_neq0.
Qed.
HB.instance Definition _ :=
  GRing.Zmodule_isRing.Build TLim
    ilmulA ilmul1r ilmulr1 ilmulDl ilmulDr ilone_neq0.

Fact ilproj_is_multiplicative i : multiplicative ('pi[TLim]_i).
Proof.
by split => /= [x y|]; rewrite [LHS]ilthrP.
Qed.
HB.instance Definition _ :=
    isRingInvLim.Build _ _ _ _ _ TLim ilproj_is_multiplicative.

HB.end.


HB.factory Record InvLim_isComRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isComRingInvLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  InvLim_isRingInvLim.Build _ _ _ _ Sys TLim.

Fact ilmulC x y : x * y = y * x.
Proof. by apply invlimE=> i; rewrite !rmorphM mulrC. Qed.
HB.instance Definition _ :=
  GRing.Ring_hasCommutativeMul.Build TLim ilmulC.

HB.end.



HB.factory Record InvLim_isUnitRingInvLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isUnitRingInvLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  InvLim_isRingInvLim.Build _ _ _ _ Sys TLim.

Definition ilunit x := `[< forall i, 'pi_i x \is a unit >].

Fact inv_isunitP x :
  (forall i, 'pi_i x \is a unit) -> isthread Sys (fun i => ('pi_i x)^-1).
Proof.
by move=> Hunit i j ilej; rewrite /= rmorphV ?(ilprojE x) // Hunit.
Qed.
Definition ilinv x : TLim :=
  if pselect (forall i, 'pi_i x \is a unit) is left Pf
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
  GRing.Ring_hasMulInverse.Build TLim
    ilmulVr ilmulrV ilunit_impl ilinv0id.

HB.end.


(** InvLimitComUnitRing. ??? *)


HB.factory Record InvLim_isIDomainInvLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isIDomainInvLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  InvLim_isUnitRingInvLim.Build _ _ _ _ Sys TLim.
HB.instance Definition _ :=
  InvLim_isComRingInvLim.Build _ _ _ _ Sys TLim.

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
  ComUnitRing_isIntegral.Build TLim ilmul_eq0.

HB.end.


HB.factory Record InvLim_isLmoduleInvLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isLmoduleInvLim R _ _ _ _ Sys TLim.

HB.instance Definition _ :=
  InvLim_isZmodInvLim.Build _ _ _ _ Sys TLim.

Fact ilscaleP r x : isthread Sys (fun i => r *: 'pi[TLim]_i x).
Proof. by move=> i j Hij; rewrite linearZ (ilprojE x). Qed.
Definition ilscale r x : TLim := ilthr (ilscaleP r x).

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
  GRing.Zmodule_isLmodule.Build R TLim ilscaleA ilscale1 ilscaleDr ilscaleDl.

Fact ilproj_is_linear i : linear 'pi[TLim]_i.
Proof.
by move=> /= r u v /=; rewrite -!/(pi_phant (Phant TLim) i) raddfD /= ilthrP.
Qed.
HB.instance Definition _ :=
  isLmodInvLim.Build R _ _ _ _ _ TLim ilproj_is_linear.

HB.end.


HB.factory Record InvLim_isLalgInvLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isLalgInvLim R _ _ _ _ Sys TLim.

Implicit Type (x y : TLim) (r : R).

HB.instance Definition _ :=
  InvLim_isRingInvLim.Build _ _ _ _ Sys TLim.
HB.instance Definition _ :=
  InvLim_isLmoduleInvLim.Build R _ _ _ _ Sys TLim.

Fact ilscaleAl r x y : r *: (x * y) = r *: x * y.
Proof.
by apply invlimE=> i /=; rewrite ilthrP !rmorphM /= ilthrP scalerAl.
Qed.
HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R TLim ilscaleAl.

(* TODO: Missing call to a non existent builder for lalgInvLimType ??? *)

HB.end.


HB.factory Record InvLim_isAlgebraInvLim
    (R : comRingType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (R : comRingType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isAlgebraInvLim R _ _ _ _ Sys TLim.

Implicit Type (x y : TLim) (r : R).

HB.instance Definition _ :=
  InvLim_isLalgInvLim.Build R _ _ _ _ Sys TLim.

Fact ilscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof.
by apply invlimE=> i /=; rewrite !(linearZ, rmorphM) /= linearZ /= !scalerAr.
Qed.
HB.instance Definition _ :=
  GRing.Lalgebra_isAlgebra.Build R TLim ilscaleAr.

(* TODO: Missing call to a non existent builder for algebraInvLim ??? *)

HB.end.


HB.factory Record InvLim_isFieldInvLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i})
    (Sys : invsys bonding)
  TLim of InvLim_isFieldInvLim _ _ _ _ Sys TLim.

HB.instance Definition _ :=
  InvLim_isIDomainInvLim.Build _ _ _ _ Sys TLim.

Fact invlim_field_axiom : field_axiom TLim.
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
    UnitRing_isField.Build TLim invlim_field_axiom.

HB.end.


Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for inverse limits                            *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.
Variable Sys : invsys bonding.

Record invlim := MkInvLim {
                     invlimthr :> forall i, Obj i;
                     _ : `[< isthread Sys invlimthr >];
                   }.

HB.instance Definition _ := [isSub for invlimthr].
HB.instance Definition _ := gen_eqMixin invlim.
HB.instance Definition _ := gen_choiceMixin invlim.

End Implem.

Notation "{ 'invlim' S }" := (invlim S).



Section InverseLimitTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj j -> Obj i.

Variable Sys : invsys bonding.
Implicit Type x y : {invlim Sys}.

Definition ilproj_impl i : {invlim Sys} -> Obj i :=
  (invlimthr (Sys := Sys))^~ i.

Lemma ilproj_implE x :
  forall i j, forall (Hij : i <= j),
      bonding Hij (ilproj_impl j x) = ilproj_impl i x.
Proof. by case: x => [thr /asboolP] /=. Qed.

Local Notation "''pi_' i" := (ilproj_impl i).

Lemma invlimP x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> eqxy; apply val_inj => /=.
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

Section Zmodule.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ := InvLim_isZmodInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Zmodule.

Section Ring.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> ringType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ := InvLim_isRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Ring.

Section ComRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> comRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isComRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End ComRing.

Section UnitRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> unitRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isUnitRingInvLim.Build _ _ _ _ Sys {invlim Sys}.
End UnitRing.

Section ComUnitRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> comUnitRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ := GRing.ComRing.on {invlim Sys}.
End ComUnitRing.

Section Linear.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isLmoduleInvLim.Build R _ _ _ _ Sys {invlim Sys}.
End Linear.

Section Lalg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isLalgInvLim.Build R _ _ _ _ Sys {invlim Sys}.
End Lalg.

Section Alg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : comRingType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isAlgebraInvLim.Build R _ _ _ _ Sys {invlim Sys}.
End Alg.

Section UnitAlg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : comRingType).
Variable Obj : I -> unitAlgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ := GRing.Algebra.on {invlim Sys}.
End UnitAlg.

Section IDomain.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> idomainType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isIDomainInvLim.Build _ _ _ _ Sys {invlim Sys}.
End IDomain.

Section Field.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> fieldType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
HB.instance Definition _ :=
  InvLim_isFieldInvLim.Build _ _ _ _ Sys {invlim Sys}.
End Field.


Section TestAlg.
Variable (R : comRingType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> algType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
Let test := GRing.Algebra.clone R _ {invlim Sys}.
End TestAlg.

Section TestField.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> fieldType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
Let test := GRing.Field.clone _ {invlim Sys}.
End TestField.


(***************************************************************************)
(** Valuation in inverse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Obj : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%N -> {additive Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : zmodInvLimType Sys.
Implicit Type (x y : TLim).

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

Lemma lt_valuatP x n : reflect ('pi_n x = 0) (Nat n < valuat x).
Proof.
apply (iffP idP); case: valuatP => [v Hv vmin /= |->].
- by rewrite ltEnatbar; apply vmin.
- by rewrite raddf0.
- apply contra_eqT; rewrite ltEnatbar -leqNgt => vlen.
  apply/contra: Hv => /eqP/(congr1 (bonding vlen)).
  by rewrite (ilprojE x) raddf0 => ->.
- by [].
Qed.

Lemma le_valuatP x n :
  reflect (forall i, (i < n)%N -> 'pi_i x = 0) (Nat n <= valuat x).
Proof.
apply (iffP idP).
- case: valuatP => [v Hv vmin /= |-> _ i _].
  + by rewrite leEnatbar => nlev i /leq_trans/(_ nlev); apply vmin.
  + by rewrite raddf0.
- case: n => // n; first exact: le0bar.
  move=> /(_ n)/(_ (ltnSn _)) /lt_valuatP.
  by case: (valuat x)=> // v; rewrite ltEnatbar leEnatbar.
Qed.

Lemma proj_gt_valuat x n : (Nat n >= valuat x) = ('pi_n x != 0).
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
by apply/invlimE=> i; rewrite raddf0; apply/lt_valuatP; rewrite valx.
Qed.

Lemma valuatN x : valuat (- x) = valuat x.
Proof.
case: (valuatP x) => [vN HvN vnmiN /= | ->]; last by rewrite oppr0 valuat0.
apply valuatNatE; first by rewrite raddfN oppr_eq0.
by move=> i /vnmiN; rewrite raddfN /= => ->; rewrite oppr0.
Qed.

Lemma valuatD x1 x2 :
  Order.min (valuat x1) (valuat x2) <= valuat (x1 + x2).
Proof.
wlog v1lev2 : x1 x2 / valuat x1 <= valuat x2.
  move=> Hlog; case (leP (valuat x1) (valuat x2)) => [|/ltW]/Hlog //.
  by rewrite addrC minC.
rewrite (min_idPl v1lev2); move: v1lev2.
case: (valuatP x1)=> [v1 Hv1 v1min|->]; last by rewrite add0r.
case: (valuatP x2)=> [v2 Hv2 v2min|->]; last by rewrite addr0 (valuatNatE Hv1).
rewrite leEnatbar => le12.
apply/le_valuatP => i Hi; rewrite raddfD /= v1min ?v2min ?addr0 //.
exact: leq_trans Hi le12.
Qed.
Lemma valuat_sum I r P (F : I ->  TLim) :
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

Lemma valuatBr s1 s2 :
  valuat s1 < valuat s2 -> valuat (s1 - s2) = valuat s1.
Proof. by rewrite -(valuatN s2) => /valuatDr. Qed.
Lemma valuatBl s1 s2 :
  valuat s2 < valuat s1 -> valuat (s1 - s2) = valuat s2.
Proof. by rewrite -(valuatN s2) addrC => /valuatDr. Qed.

End Valuation.


Section ValuationLmodRing.

Variable R : ringType.
Variable Obj : nat -> lmodType R.
Variable bonding : forall i j : nat, (i <= j)%N -> {linear Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : lmodInvLimType Sys.
Implicit Types (r : R) (x y : TLim).

Lemma valuat_scale r x : valuat x <= valuat (r *: x).
Proof.
case: (valuatP x)=> [v Hv vmin|->]; last by rewrite scaler0 valuat0.
apply/le_valuatP => i {}/vmin pix0.
by rewrite linearZ /= pix0 scaler0.
Qed.

End ValuationLmodRing.


Section ValuationLmodUnitRing.

Variable R : unitRingType.
Variable Obj : nat -> lmodType R.
Variable bonding : forall i j : nat, (i <= j)%N -> {linear Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : lmodInvLimType Sys.
Implicit Types (r : R) (x y : TLim).

Lemma valuat_scale_unit r x :
  r \is a GRing.unit -> valuat (r *: x) = valuat x.
Proof.
move=> runit; apply le_anti; rewrite valuat_scale /=.
by rewrite -{2}(scale1r x) -(mulVr runit) -scalerA valuat_scale.
Qed.

End ValuationLmodUnitRing.

Section ValuationRing.

Variable Obj : nat -> ringType.
Variable bonding : forall i j : nat, (i <= j)%N -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type (x y : TLim).

Lemma valuat1 : valuat (1 : TLim) = Nat 0.
Proof. by apply valuatNatE => [|i //]; rewrite rmorph1 oner_neq0. Qed.

Lemma valuatMl x1 x2 : valuat x1 <= valuat (x1 * x2).
Proof.
case: (valuatP x1)=> [v1 Hv1 v1min|->]; last by rewrite mul0r valuat0 lebarI.
by apply/le_valuatP => i /v1min; rewrite rmorphM /= => ->; rewrite mul0r.
Qed.
Lemma valuatMr x1 x2 : valuat x2 <= valuat (x1 * x2).
Proof.
case: (valuatP x2)=> [v2 Hv2 v2min|->]; last by rewrite mulr0 valuat0 lebarI.
by apply/le_valuatP => i /v2min; rewrite rmorphM /= => ->; rewrite mulr0.
Qed.

Lemma valuatM x1 x2 : Order.max (valuat x1) (valuat x2) <= valuat (x1 * x2).
Proof. by rewrite leUx valuatMl valuatMr. Qed.

Lemma valuat_prod I r P (F : I ->  TLim) :
  \join_(i <- r | P i) valuat (F i) <= valuat (\prod_(i <- r | P i) F i).
Proof.
apply: (big_ind2 (fun x v => v <= valuat x)); rewrite ?valuat1 //=.
by move=> x1 v1 x2 v2 H1 H2; apply: (le_trans (leU2 _ _) (valuatM x1 x2)).
Qed.

End ValuationRing.


Section CommHugeOp.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j : I, i <= j -> Obj j -> Obj i.
Variable Sys : invsys bonding.
Variable TLim : invLimType Sys.

Variable (C : choiceType).
Variables (idx : TLim) (op : Monoid.com_law idx).

Implicit Type F : C -> TLim.
Implicit Types (x y z t : TLim).

Definition invar i x := forall s, 'pi_i (op x s) = 'pi_i s.
Definition is_ilopable F :=
  `[< forall i, exists S : {fset C}, forall c, c \notin S -> invar i (F c)>].
Lemma ilopand_spec F :
  is_ilopable F ->
  forall i, { f : {fset C} | f =i predC (fun c => `[< invar i (F c)>]) }.
Proof.
move=> H i; move/asboolP/(_ i): H => /cid [s Hs].
have key : Datatypes.unit by [].
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

Definition HugeOp F : TLim :=
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

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj j -> Obj i}.
Variable Sys : invsys bonding.
Variable TLim : zmodInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> TLim.
Implicit Types (s x y z t : TLim).

Check TLim : nmodType.

Let add_law : Monoid.com_law 0 := (+%R : TLim -> TLim -> TLim).
(* Let add_law := [the Monoid.com_law of TLim]. *)

Definition is_summable F := is_ilopable add_law F.
Definition summand F (sm : is_summable F) := ilopand sm.
Definition HugeSum F : TLim := HugeOp add_law F.

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

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> comRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj j -> Obj i}.
Variable Sys : invsys bonding.
Variable TLim : comRingInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> TLim.
Implicit Types (s x y z t : TLim).

Let mul_law : Monoid.com_law 1 := ( *%R : TLim -> TLim -> TLim).

Definition is_prodable F := is_ilopable mul_law F.
Definition prodand F (sm : is_prodable F) := ilopand sm.
Definition HugeProd F : TLim := HugeOp mul_law F.

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
