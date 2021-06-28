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
From mathcomp Require Import order finmap bigop.

Require Import natbar directed.


Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

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

Variables (disp : unit) (I : porderType disp).

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

Definition cone of invsys := fun T (mors : forall i, T -> Ob i) =>
  forall i j, forall (Hij : i <= j), bonding Hij \o mors j =1 mors i.

Lemma coneE Sys T (mors : forall i, T -> Ob i) : cone Sys mors ->
  forall i j (Hij : i <= j) x, bonding Hij (mors j x) = mors i x.
Proof. by rewrite /cone => H i j le_ij x; rewrite -(H i j le_ij). Qed.

Lemma cone_thr Sys T (mors : forall i, T -> Ob i) :
  cone Sys mors -> forall t : T, isthread Sys (mors ^~ t).
Proof. by rewrite /cone => Hf t i j Hij; apply: Hf. Qed.

End InverseSystem.


(***************************************************************************)
(** Interface for inverse limits                                           *)
(*                                                                         *)
(***************************************************************************)
Module InvLim.

Section ClassDefs.

Variables (disp : unit) (I : porderType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.

Record mixin_of (TLim : Type) := Mixin {
  invlim_proj : forall i, TLim -> Ob i;
  invlim_ind  : forall (T : Type) (f : forall i, T -> Ob i),
      (cone Sys f) -> T -> TLim;
  _ : cone Sys invlim_proj;
  _ : forall T (f : forall i, T -> Ob i) (Hcone : cone Sys f),
      forall i, invlim_proj i \o invlim_ind Hcone =1 f i;
  _ : forall T (f : forall i, T -> Ob i) (Hcone : cone Sys f),
      forall (ind : T -> TLim),
        (forall i, invlim_proj i \o ind =1 f i) ->
        ind =1 invlim_ind Hcone
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

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.

End ClassDefs.


Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation invLimType := type.
Notation InvLimMixin := Mixin.

Section InternalTheory.

Variables (disp : unit) (I : porderType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.
Variable ilT : invLimType Sys.

Definition pi_phant of phant ilT := invlim_proj (mixin (class ilT)).
Local Notation "\pi" := (pi_phant (Phant ilT)).
Definition ind_phant of phant ilT := invlim_ind (mixin (class ilT)).
Local Notation "\ind" := (ind_phant (Phant ilT)).

Lemma ilprojP : cone Sys \pi.
Proof. by rewrite /pi_phant; case: ilT => /= [TLim [eqM []]]. Qed.

Lemma ilprojE (x : ilT) :
  forall i j, forall (Hij : i <= j), bonding Hij (\pi j x) = \pi i x.
Proof.
move=> i j Hij.
by rewrite -/((bonding Hij \o (pi_phant (Phant ilT)) j) x) ilprojP.
Qed.

Lemma ind_commute T (f : forall i, T -> Ob i) (Hcone : cone Sys f) :
  forall i, \pi i \o \ind Hcone =1 f i.
Proof. by rewrite /pi_phant /ind_phant; case: ilT => /= [TLim [eqM []]]. Qed.

Lemma piindE  T (f : forall i, T -> Ob i) (Hcone : cone Sys f) i x :
  \pi i (\ind Hcone x) = f i x.
Proof. exact: ind_commute. Qed.

Lemma ind_uniq T (f : forall i, T -> Ob i) (Hcone : cone Sys f) :
  forall (ind : T -> ilT),
    (forall i, \pi i \o ind =1 f i) -> ind =1 \ind Hcone.
Proof.
rewrite /pi_phant /ind_phant.
case: ilT => /= [TLim [eqM /= [pi ind comp comm uniq]]] indT commT t /=.
by apply uniq; apply commT.
Qed.

End InternalTheory.

End Exports.
End InvLim.
Export InvLim.Exports.

Arguments ilprojP {disp I Ob bonding} [Sys].

Notation InvLimType T m := (@InvLim.pack _ _ _ _ _ T m _ _ id).
Notation "[ 'invLimType' 'of' T 'for' cT ]" :=
  (@InvLim.clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'invLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'invLimType' 'of' T ]" :=
  (@InvLim.clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'invLimType'  'of'  T ]") : form_scope.

Notation "''pi_' i" := (pi_phant (Phant _) i).
Notation "''pi[' T ']_' i" := (pi_phant (Phant T) i)
                              (at level 8, i at level 2, only parsing).
Notation "\ind" := (ind_phant (Phant _)).
Notation "\ind[ T ]" := (ind_phant (Phant T)) (only parsing).


Section Theory.

Variables (disp : unit) (I : porderType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.
Variable ilT : invLimType Sys.

Lemma invlimE (x y : ilT) : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq.
pose fx : forall i : I, unit -> Ob i := fun i tt => 'pi_i x.
have compf : cone Sys fx.
  by rewrite /fx => i j le_ij tt /=; rewrite ilprojE.
pose ind z : unit -> ilT := fun tt => z.
have Huniqy i : 'pi_i \o ind y =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
have Huniqx i : 'pi_i \o ind x =1 fx i by move=> tt /=; rewrite /ind /fx Heq.
move: (ind_uniq compf Huniqx tt) (ind_uniq compf Huniqy tt).
by rewrite /ind => -> ->.
Qed.

Lemma from_thread_spec (thr : forall i : I, Ob i) :
  isthread Sys thr -> { t : ilT | forall i, 'pi_i t = thr i }.
Proof.
rewrite /isthread => Hhtr.
pose f : forall i : I, unit -> Ob i := fun i tt => thr i.
have compf : cone Sys f by rewrite /f => i j le_ij tt /=.
by exists (\ind compf tt) => i; rewrite piindE.
Qed.
Definition ilthr thr (Hthr : isthread Sys thr) :=
  let: exist res _ := from_thread_spec Hthr in res.

Lemma ilthrP thr (Hthr : isthread Sys thr) :
  forall i, 'pi_i (ilthr Hthr) = thr i.
Proof. by rewrite /ilthr; case: from_thread_spec. Qed.

Lemma invlim_exE (x y : ilT) :
  (forall i, exists2 i0, i0 >= i & 'pi_i0 x = 'pi_i0 y) -> x = y.
Proof.
move=> Heq; apply invlimE => i.
move: Heq => /( _ i) [i0 le_ii0] /(congr1 (bonding le_ii0)).
by rewrite !ilprojE.
Qed.

End Theory.
Arguments ilthr {disp I Ob bonding Sys ilT thr}.


Section InvLimitDirected.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.
Variable ilT : invLimType Sys.

Lemma invlim_geE b (x y : ilT) :
  (forall i, i >= b -> 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq; apply invlim_exE => i.
by have:= directedP i b => [][j le_ij {}/Heq Heq]; exists j.
Qed.

End InvLimitDirected.
Arguments invlim_geE {disp I Ob bonding Sys ilT}.


Section InvLimitEqType.

Variables (disp : unit) (I : porderType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.

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


Open Scope ring_scope.
Import GRing.
Import GRing.Theory.


(****************************************************************************)
(**  Interface for inverse limits in various algebraic categories           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

Module ZmodInvLim.
Section ClassDef.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : invsys bonding.

Record mixin_of (T : zmodType) (mixin : InvLim.mixin_of Sys T) := Mixin {
  _ : forall i, additive (InvLim.invlim_proj mixin i : T -> Ob i)
}.
(* TODO EtaMixin *)

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base  : Zmodule.class_of T;
  mixin : InvLim.mixin_of Sys (Zmodule.Pack base);
  compadd : mixin_of mixin;
}.
Unset Primitive Projections.
Definition base2 M (c : class_of M) := InvLim.Class (base c) (mixin c).
Local Coercion base : class_of >-> Zmodule.class_of.
Local Coercion base2 : class_of >-> InvLim.class_of.
Local Coercion mixin : class_of >-> InvLim.mixin_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun fT f & phant_id (InvLim.mixin (InvLim.class (Sys := Sys) fT)) f =>
  fun    m => Pack (@Class T b f m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition invlimType := @InvLim.Pack _ _ _ _ _ cT class.

Definition zmod_invlimType := @Zmodule.Pack invlimType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion base2 : class_of >-> InvLim.class_of.
Coercion mixin : class_of >-> InvLim.mixin_of.
Coercion compadd : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion invlimType : type >-> InvLim.type.
Canonical invlimType.

(*
Canonical zmod_invlimType.
 *)

Notation zmodInvLimType := type.
Notation ZmodInvLimType T m := (@pack _ _ _ _ _ T _ _ id _ _ id m).
Notation ZmodInvLimMixin := Mixin.
Notation "[ 'zmodInvLimType' 'of' T 'for' cT ]" :=
  (@clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'zmodInvLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodInvLimType' 'of' T ]" := (@clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'zmodInvLimType'  'of'  T ]") : form_scope.
End Exports.

End ZmodInvLim.
Export ZmodInvLim.Exports.

Section ZmodInvLimTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : zmodInvLimType Sys.
Implicit Type x y : TLim.

Fact ilproj_is_additive i : additive ('pi_i : TLim -> Ob i).
Proof. by case: TLim => T [b m [Hadd]]; rewrite /pi_phant. Qed.
Canonical ilproj_additive i :=  Additive (ilproj_is_additive i).

Lemma il_neq0 x : x != 0 -> exists i, 'pi_i x != 0.
Proof. by move/invlimPn=> [i]; rewrite raddf0 => Hi; exists i. Qed.

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> Ob i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_additive : additive (\ind Hcone : T -> TLim).
Proof.
by move=> t u; apply invlimE=> i; rewrite raddfB /= !piindE raddfB.
Qed.
Canonical ilind_additive := Additive ilind_is_additive.

End UniversalProperty.
End ZmodInvLimTheory.


Module RingInvLim.
Section ClassDef.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Record mixin_of (T : ringType) (mixin : InvLim.mixin_of Sys T) := Mixin {
  _ : forall i, multiplicative (InvLim.invlim_proj mixin i : T -> Ob i)
}.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base  : Ring.class_of T;
  mixin : InvLim.mixin_of Sys (Ring.Pack base);
  compadd : ZmodInvLim.mixin_of mixin;
  compmul : mixin_of mixin;
}.
Unset Primitive Projections.
Definition base2 M (c : class_of M) := ZmodInvLim.Class (compadd c).
Local Coercion base : class_of >-> Ring.class_of.
Local Coercion base2 : class_of >-> ZmodInvLim.class_of.
Local Coercion mixin : class_of >-> InvLim.mixin_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun rT r & phant_id (InvLim.mixin (InvLim.class (Sys := Sys) rT)) r =>
  fun zT z & phant_id (ZmodInvLim.compadd (ZmodInvLim.class (Sys := Sys) zT)) z =>
      fun m => Pack (@Class T b r z m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition invlimType := @InvLim.Pack _ _ _ _ _ cT class.
Definition zmodInvlimType := @ZmodInvLim.Pack _ _ _ _ _ cT class.

Definition ring_invlimType := @Ring.Pack invlimType class.
Definition ring_zmodInvlimType := @Ring.Pack zmodInvlimType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion base2 : class_of >-> ZmodInvLim.class_of.
Coercion mixin : class_of >-> InvLim.mixin_of.
Coercion compadd : class_of >-> ZmodInvLim.mixin_of.
Coercion compmul : class_of >-> mixin_of.
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
Coercion invlimType : type >-> InvLim.type.
Canonical invlimType.
Coercion zmodInvlimType : type >-> ZmodInvLim.type.
Canonical zmodInvlimType.

(*
Canonical ring_invlimType.
Canonical ring_zmodInvlimType.
 *)

Notation ringInvLimType := type.
Notation RingInvLimType T m := (@pack _ _ _ _ _ T _ _ id _ _ id _ _ id m).
Notation RingInvLimMixin := Mixin.
Notation "[ 'ringInvLimType' 'of' T 'for' cT ]" :=
  (@clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'ringInvLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringInvLimType' 'of' T ]" :=
  (@clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'ringInvLimType'  'of'  T ]") : form_scope.
End Exports.

End RingInvLim.
Export RingInvLim.Exports.


Section RingInvLimTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.

Fact ilproj_is_multiplicative i : multiplicative ('pi_i : TLim -> Ob i).
Proof. by case: TLim => T [b m [madd [mmult]]]; rewrite /pi_phant /=. Qed.
Canonical ilproj_rmorphism i := AddRMorphism (ilproj_is_multiplicative i).

Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism T -> Ob i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_multiplicative : multiplicative (\ind[TLim] Hcone).
Proof.
by split => [/= t u|]; apply invlimE=> i;
  rewrite !piindE ?rmorph1 ?rmorphM //= !piindE.
Qed.
Canonical ilind_rmorphism := AddRMorphism ilind_is_multiplicative.

End UniversalProperty.
End RingInvLimTheory.


Module ComRingInvLim.
Section ClassDef.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base  : RingInvLim.class_of Sys T;
  mixin : commutative (Ring.mul base)
}.
Unset Primitive Projections.

Definition base2 M (c : class_of M) := ComRing.Class (@mixin M c).
Local Coercion base : class_of >-> RingInvLim.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (RingInvLim.class (Sys := Sys) bT) b =>
  fun rT r & phant_id (ComRing.mixin (ComRing.class rT)) r =>
    Pack (@Class T b r).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition invlimType := @InvLim.Pack _ _ _ _ _ cT class.
Definition zmodInvlimType := @ZmodInvLim.Pack _ _ _ _ _ cT class.
Definition ringInvlimType := @RingInvLim.Pack _ _ _ _ _ cT class.

Definition comring_invlimType := @ComRing.Pack invlimType class.
Definition comring_zmodInvlimType := @ComRing.Pack zmodInvlimType class.
Definition comring_ringInvlimType := @ComRing.Pack ringInvlimType class.

End ClassDef.

Module Exports.
Coercion base : class_of >->  RingInvLim.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion mixin : class_of >-> commutative.
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

Coercion invlimType : type >-> InvLim.type.
Canonical invlimType.
Coercion zmodInvlimType : type >-> ZmodInvLim.type.
Canonical zmodInvlimType.
Coercion ringInvlimType : type >-> RingInvLim.type.
Canonical ringInvlimType.

(*
Canonical comring_invlimType.
Canonical comring_zmodInvlimType.
Canonical comring_ringInvlimType.
 *)

Notation comRingInvLimType := type.
Notation ComRingInvLimType T := (@pack _ _ _ _ _ T _ _ id _ _ id).
Notation "[ 'comRingInvLimType' 'of' T 'for' cT ]" :=
  (@clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'comRingInvLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingInvLimType' 'of' T ]" :=
  (@clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'comRingInvLimType'  'of'  T ]") : form_scope.

End Exports.
End ComRingInvLim.
Export ComRingInvLim.Exports.


Module LmodInvLim.
Section ClassDef.

Variable R : ringType.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Ob j -> Ob i}.
Variable Sys : invsys bonding.

Record mixin_of (T : lmodType R) (mixin : InvLim.mixin_of Sys T) := Mixin {
  _ : forall i, linear (InvLim.invlim_proj mixin i : T -> Ob i)
}.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base  : Lmodule.class_of R T;
  mixin : InvLim.mixin_of Sys (Lmodule.Pack (Phant R) base);
  compadd : ZmodInvLim.mixin_of mixin;
  compscal : mixin_of mixin;
}.
Unset Primitive Projections.

Definition base2 M (c : class_of M) := ZmodInvLim.Class (compadd c).
Local Coercion base : class_of >-> Lmodule.class_of.
Local Coercion base2 : class_of >-> ZmodInvLim.class_of.
Local Coercion mixin : class_of >-> InvLim.mixin_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Lmodule.class (phR := Phant R) bT) b =>
  fun rT r & phant_id (InvLim.mixin (InvLim.class (Sys := Sys) rT)) r =>
  fun zT z & phant_id (ZmodInvLim.compadd (ZmodInvLim.class (Sys := Sys) zT)) z =>
      fun m => Pack (@Class T b r z m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition lmodType := @Lmodule.Pack R (Phant R) cT class.

Definition invlimType := @InvLim.Pack _ _ _ _ _ cT class.
Definition zmodInvlimType := @ZmodInvLim.Pack _ _ _ _ _ cT class.

Definition lmod_invlimType :=
  @Lmodule.Pack R (Phant R) invlimType class.
Definition lmod_zmodInvlimType :=
  @Lmodule.Pack R (Phant R) zmodInvlimType class.
(* TODO more join *)

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lmodule.class_of.
Coercion base2 : class_of >-> ZmodInvLim.class_of.
Coercion mixin : class_of >-> InvLim.mixin_of.
Coercion compadd : class_of >-> ZmodInvLim.mixin_of.
Coercion compscal : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.

Coercion invlimType : type >-> InvLim.type.
Canonical invlimType.
Coercion zmodInvlimType : type >-> ZmodInvLim.type.
Canonical zmodInvlimType.

Notation lmodInvLimType := type.
Notation LmodInvLimType R T m := (@pack R _ _ _ _ _ T _ _ id _ _ id _ _ id m).
Notation LmodInvLimMixin := Mixin.
Notation "[ 'lmodInvLimType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'lmodInvLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'lmodInvLimType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'lmodInvLimType'  'of'  T ]") : form_scope.
End Exports.

End LmodInvLim.
Export LmodInvLim.Exports.


Section LmodInvLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : lmodInvLimType Sys.

Fact ilproj_is_linear i : linear ('pi_i : TLim -> Ob i).
Proof. by case: TLim => T [b m c [lin]]; rewrite /pi_phant. Qed.
Canonical ilproj_linear i := AddLinear (ilproj_is_linear i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear T -> Ob i}).
Hypothesis Hcone : cone Sys f.

Fact ilind_is_linear : linear (\ind Hcone : T -> TLim).
Proof.
move=> t u v; apply invlimE => i.
by rewrite !raddfD /= !piindE !linearZ /= piindE.
Qed.
Canonical ilind_linear := AddLinear ilind_is_linear.

End UniversalProperty.
End LmodInvLimTheory.


Module LalgInvLim.
Section ClassDef.

Variables (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base  : Lalgebra.class_of R T;
  mixin : InvLim.mixin_of Sys (Lalgebra.Pack (Phant R) base);
  compadd : ZmodInvLim.mixin_of mixin;
  compscal : LmodInvLim.mixin_of mixin;
  compmul : RingInvLim.mixin_of mixin;
}.
Unset Primitive Projections.

Definition base2 M (c : class_of M) := RingInvLim.Class (compadd c) (compmul c).
Definition base3 M (c : class_of M) :=
  LmodInvLim.Class (base := base c) (compadd c) (compscal c).

Local Coercion base : class_of >-> Lalgebra.class_of.
Local Coercion base2 : class_of >-> RingInvLim.class_of.
Local Coercion base3 : class_of >-> LmodInvLim.class_of.
Local Coercion mixin : class_of >-> InvLim.mixin_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack :=
  fun bT b & phant_id (Lalgebra.class (phR := Phant R) bT) b =>
  fun ilT il & phant_id (InvLim.mixin (InvLim.class (Sys := Sys) ilT)) il =>
  fun zT z & phant_id (ZmodInvLim.compadd (ZmodInvLim.class (Sys := Sys) zT)) z =>
  fun lT l & phant_id (LmodInvLim.compscal (LmodInvLim.class (Sys := Sys) lT)) l =>
  fun mT m & phant_id (RingInvLim.compmul (RingInvLim.class (Sys := Sys) mT)) m =>
      Pack (@Class T b il z l m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition lmodType := @Lmodule.Pack R (Phant R) cT class.
Definition lalgType := @Lalgebra.Pack R (Phant R) cT class.

Definition invlimType := @InvLim.Pack _ _ _ _ _ cT class.
Definition zmodInvlimType := @ZmodInvLim.Pack _ _ _ _ _ cT class.
Definition ringInvlimType := @RingInvLim.Pack _ _ _ _ _ cT class.
Definition lmodInvlimType := @LmodInvLim.Pack R _ _ _ _ _ cT class.

Definition lalg_invlimType := @Lalgebra.Pack R (Phant R) invlimType class.
(* TODO more join *)

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lalgebra.class_of.
Coercion base2 : class_of >-> RingInvLim.class_of.
Coercion base3 : class_of >-> LmodInvLim.class_of.
Coercion mixin : class_of >-> InvLim.mixin_of.
Coercion compadd : class_of >-> ZmodInvLim.mixin_of.
Coercion compscal : class_of >-> LmodInvLim.mixin_of.
Coercion  compmul : class_of >-> RingInvLim.mixin_of.
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
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.

Coercion invlimType : type >-> InvLim.type.
Canonical invlimType.
Coercion zmodInvlimType : type >-> ZmodInvLim.type.
Canonical zmodInvlimType.
Coercion ringInvlimType : type >-> RingInvLim.type.
Canonical ringInvlimType.
Coercion lmodInvlimType : type >-> LmodInvLim.type.
Canonical lmodInvlimType.

Notation lalgInvLimType := type.
Notation LalgInvLimType R T :=
  (@pack R _ _ _ _ _ T _ _ id _ _ id _ _ id _ _ id _ _ id).
Notation "[ 'lalgInvLimType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'lalgInvLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'lalgInvLimType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'lalgInvLimType'  'of'  T ]") : form_scope.
End Exports.

End LalgInvLim.
Export LalgInvLim.Exports.

Section LAlgInvLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : lalgInvLimType Sys.
Canonical ilproj_lrmorphism i := [lrmorphism of 'pi[TLim]_i].

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism T -> Ob i}).
Hypothesis Hcone : cone Sys f.
Canonical ilind_lrmorphism := [lrmorphism of \ind[TLim] Hcone].

End UniversalProperty.
End LAlgInvLimTheory.




(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

Module InvLimitZmod.
Section InvLimitZmod.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : invLimType Sys.
Implicit Type x y : TLim.

Fact ilzeroP : isthread Sys (fun i => 0 : Ob i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : TLim := ilthr ilzeroP.

Fact iloppP x : isthread Sys (fun i => - ('pi_i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : TLim := ilthr (iloppP x).

Fact iladdP x y : isthread Sys (fun i => 'pi_i x + 'pi_i y).
Proof. by move=> i j Hij; rewrite raddfD (ilprojE x) (ilprojE y). Qed.
Definition iladd x y : TLim := ilthr (iladdP x y).

Program Definition invlim_zmodMixin of phant TLim :=
  @ZmodMixin TLim ilzero ilopp iladd _ _ _ _.
Next Obligation. by move=> a b c; apply invlimE=> i; rewrite !ilthrP addrA. Qed.
Next Obligation. by move=> a b; apply invlimE=> i; rewrite !ilthrP addrC. Qed.
Next Obligation. by move=> b; apply invlimE=> i; rewrite !ilthrP add0r. Qed.
Next Obligation. by move=> b; apply invlimE=> i; rewrite !ilthrP addNr. Qed.

(* Not global canonical but accessible by [zmodMixin of ... by <-] *)
(* A mettre dans un module pour avoir le canonical local *)
Local Canonical invlim_zmodType :=
  Eval hnf in ZmodType TLim (invlim_zmodMixin (Phant TLim)).

Program Definition invlim_zmodInvLimMixin of (phant TLim) :=
  ZmodInvLimMixin (mixin := InvLim.class TLim) _.
Next Obligation.
move=> /= x y /=.  (* Coq needs help tofind where to rewrite ilthrP *)
by rewrite [LHS]ilthrP [X in _ + X]ilthrP.
Qed.
Local Canonical invlim_zmodInvLimType :=
  Eval hnf in ZmodInvLimType TLim (invlim_zmodInvLimMixin (Phant TLim)).

End InvLimitZmod.
End InvLimitZmod.

Notation "[ 'zmodMixin' 'of' U 'by' <- ]" :=
  (InvLimitZmod.invlim_zmodMixin (Phant U))
  (at level 0, format "[ 'zmodMixin'  'of'  U  'by'  <- ]") : form_scope.
Notation "[ 'zmodInvLimMixin' 'of' U 'by' <- ]" :=
  (InvLimitZmod.invlim_zmodInvLimMixin (Phant U))
  (at level 0, format "[ 'zmodInvLimMixin'  'of'  U  'by'  <- ]") : form_scope.


Module InvLimitRing.
Section InvLimitRing.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : invLimType Sys.
Implicit Type x y : TLim.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_zmodinvlimType :=
  Eval hnf in ZmodInvLimType TLim [zmodInvLimMixin of TLim by <-].

Fact iloneP : isthread Sys (fun i => 1 : Ob i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : TLim := ilthr iloneP.

Fact ilmulP x y : isthread Sys (fun i => 'pi_i x * 'pi_i y).
Proof. by move=> i j Hij; rewrite rmorphM (ilprojE x) (ilprojE y). Qed.
Definition ilmul x y : TLim := ilthr (ilmulP x y).

Program Definition invlim_ringMixin of phant TLim :=
  @RingMixin _ ilone ilmul _ _ _ _ _ _.
Next Obligation. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrA. Qed.
Next Obligation. by move=> a; apply invlimE=> i; rewrite !ilthrP mul1r. Qed.
Next Obligation. by move=> a; apply invlimE=> i; rewrite !ilthrP mulr1. Qed.
Next Obligation. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrDl. Qed.
Next Obligation. by move=> a b c; apply invlimE=> i; rewrite !ilthrP mulrDr. Qed.
Next Obligation.
apply/negP => /eqP/(congr1 (fun x => 'pi_(invsys_inh Sys) x)) /= /eqP.
by rewrite !ilthrP; exact/negP/oner_neq0.
Qed.
Local Canonical invlim_ringType :=
  Eval hnf in RingType TLim (invlim_ringMixin (Phant TLim)).

Program Definition invlim_ringInvLimMixin of (phant TLim) :=
  RingInvLimMixin (mixin := InvLim.class TLim) _.
Next Obligation.
by split => /= [x y|]; rewrite [LHS]ilthrP.
Qed.
Local Canonical invlim_ringInvLimType :=
  Eval hnf in RingInvLimType TLim (invlim_ringInvLimMixin (Phant TLim)).

End InvLimitRing.
End InvLimitRing.

Notation "[ 'ringMixin' 'of' U 'by' <- ]" :=
  (InvLimitRing.invlim_ringMixin (Phant U))
  (at level 0, format "[ 'ringMixin'  'of'  U  'by'  <- ]") : form_scope.
Notation "[ 'ringInvLimMixin' 'of' U 'by' <- ]" :=
  (InvLimitRing.invlim_ringInvLimMixin (Phant U))
  (at level 0, format "[ 'ringInvLimMixin'  'of'  U  'by'  <- ]") : form_scope.


Module InvLimitComRing.
Section InvLimitComRing.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type x y : TLim.

Fact ilmulC x y : x * y = y * x.
Proof. by apply invlimE=> i; rewrite !rmorphM mulrC. Qed.
Definition invlim_comRingMixin of phant TLim := ilmulC.
Local Canonical invlim_comRingType :=
  Eval hnf in ComRingType TLim (invlim_comRingMixin (Phant TLim)).
Local Canonical invlim_comRingInvLimType :=
  Eval hnf in ComRingInvLimType TLim.

End InvLimitComRing.
End InvLimitComRing.

Notation "[ 'comRingMixin' 'of' U 'by' <- ]" :=
  (InvLimitComRing.invlim_comRingMixin (Phant U))
  (at level 0, format "[ 'comRingMixin'  'of'  U  'by'  <- ]") : form_scope.


Module InvLimitUnitRing.
Section InvLimitUnitRing.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type x y : TLim.

Definition ilunit x := `[forall i, 'pi_i x \is a unit].

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
move=> x /forallbP Hinv; apply invlimE=> i.
rewrite /ilinv; case: pselect => /= [H |/(_ Hinv)//].
by rewrite rmorphM rmorph1 /= !ilthrP mulVr.
Qed.
Fact ilmulrV : {in ilunit, right_inverse 1 ilinv *%R}.
Proof.
move=> x /forallbP Hinv; apply invlimE=> i.
rewrite /ilinv; case: pselect => /= [H |/(_ Hinv)//].
by rewrite rmorphM rmorph1 /= !ilthrP mulrV.
Qed.
Fact ilunit_impl x y : y * x = 1 /\ x * y = 1 -> ilunit x.
Proof.
move=> [Hxy Hyx]; apply/forallbP => i; apply/unitrP.
by exists ('pi_i y); rewrite -!rmorphM Hxy Hyx /= rmorph1.
Qed.
Fact ilinv0id : {in [predC ilunit], ilinv =1 id}.
Proof.
move=> x; rewrite inE /= => /forallbP Hx.
by rewrite /ilinv; case: pselect => /= [/= H|//]; have:= Hx H.
Qed.
Definition invlim_unitRingMixin of (phant TLim) :=
  Eval hnf in UnitRingMixin ilmulVr ilmulrV ilunit_impl ilinv0id.
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim (invlim_unitRingMixin (Phant TLim)).

Lemma ilunitP x :
  reflect (forall i, 'pi_i x \is a unit) (x \is a unit).
Proof. exact: forallbP. Qed.

End InvLimitUnitRing.
End InvLimitUnitRing.

Notation "[ 'unitRingMixin' 'of' U 'by' <- ]" :=
  (InvLimitUnitRing.invlim_unitRingMixin (Phant U))
  (at level 0, format "[ 'unitRingMixin'  'of'  U  'by'  <- ]") : form_scope.

Definition ilunitP := InvLimitUnitRing.ilunitP.

(** No more useful
Section InvLimitComUnitRing.

Variables (disp : unit) (I : porderType disp).
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : invLimType Sys.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical TLim_comRingType :=
  Eval hnf in ComRingType TLim [comRingMixin of TLim by <-].
Local Canonical invlim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].

End InvLimitComUnitRing.
*)


Module InvLimitIDomain.
Section InvLimitIDomain.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type (x y : TLim).

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

Definition invlim_idomainMixin of phant TLim := ilmul_eq0.

End InvLimitIDomain.
End InvLimitIDomain.

Notation "[ 'idomainMixin' 'of' U 'by' <- ]" :=
  (InvLimitIDomain.invlim_idomainMixin (Phant U))
  (at level 0, format "[ 'idomainMixin'  'of'  U  'by'  <- ]") : form_scope.


Module InvLimitLmod.
Section InvLimitLmod.

Variables (R : ringType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : zmodInvLimType Sys.
Implicit Type (x y : TLim) (r : R).

Fact ilscaleP r x : isthread Sys (fun i => r *: 'pi_i x).
Proof. by move=> i j Hij; rewrite linearZ (ilprojE x). Qed.
Definition ilscale r x : TLim := ilthr (ilscaleP r x).

Program Definition invlim_lmodMixin of phant TLim :=
  @LmodMixin R [zmodType of TLim] ilscale _ _ _ _.
Next Obligation. by apply invlimE=> i /=; rewrite !ilthrP scalerA. Qed.
Next Obligation. by move=> x; apply invlimE=> i; rewrite !ilthrP scale1r. Qed.
Next Obligation.
move=> r x y; apply invlimE=> i.
rewrite raddfD ilthrP raddfD scalerDr /=.
by rewrite [X in _ = X + _]ilthrP [X in _ = _ + X]ilthrP /=.
Qed.
Next Obligation.
move=> r s; apply invlimE=> i; rewrite !ilthrP scalerDl raddfD /=.
by rewrite [X in _ = X + _]ilthrP [X in _ = _ + X]ilthrP /=.
Qed.

Local Canonical invlim_lmodType :=
  Eval hnf in LmodType R TLim (invlim_lmodMixin (Phant TLim)).

Program Definition invlim_lmodInvLimMixin of (phant TLim) :=
  LmodInvLimMixin (mixin := InvLim.class TLim) _.
Next Obligation.
by move=> /= r u v /=; rewrite -!/(pi_phant (Phant TLim) i) raddfD /= ilthrP.
Qed.
Local Canonical invlim_lmodInvLimType :=
  Eval hnf in LmodInvLimType R TLim (invlim_lmodInvLimMixin (Phant TLim)).

End InvLimitLmod.
End InvLimitLmod.

Notation "[ 'lmodMixin' 'of' U 'by' <- ]" :=
  (InvLimitLmod.invlim_lmodMixin (Phant U))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <- ]") : form_scope.
Notation "[ 'lmodInvLimMixin' 'of' U 'by' <- ]" :=
  (InvLimitLmod.invlim_lmodInvLimMixin (Phant U))
  (at level 0, format "[ 'lmodInvLimMixin'  'of'  U  'by'  <- ]") : form_scope.


Module InvLimitLalg.
Section InvLimitLalg.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type (x y : TLim) (r : R).

Local Canonical invlim_lmodType :=
  Eval hnf in LmodType R TLim [lmodMixin of TLim by <-].
Local Canonical invlim_lmodInvlimType :=
  Eval hnf in LmodInvLimType R TLim [lmodInvLimMixin of TLim by <-].

Fact ilscaleAl r x y : r *: (x * y) = r *: x * y.
Proof.
by apply invlimE=> i /=; rewrite ilthrP !rmorphM /= ilthrP scalerAl.
Qed.
Definition invlim_lalgMixin of phant TLim := ilscaleAl.
Local Canonical invlim_lalgType := Eval hnf in LalgType R TLim ilscaleAl.
Local Canonical invlim_lalgInvLimType := Eval hnf in LalgInvLimType R TLim.

End InvLimitLalg.
End InvLimitLalg.

Notation "[ 'lalgMixin' 'of' U 'by' <- ]" :=
  (InvLimitLalg.invlim_lalgMixin (Phant U))
  (at level 0, format "[ 'lalgMixin'  'of'  U  'by'  <- ]") : form_scope.



Module InvLimitAlg.
Section InvLimitAlg.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : lalgInvLimType Sys.
Implicit Type (x y : TLim) (r : R).

Fact ilscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof.
by apply invlimE=> i /=; rewrite !(linearZ, rmorphM) /= scalerAr.
Qed.
Definition invlim_algMixin of phant TLim := ilscaleAr.
Local Canonical invlim_algType := Eval hnf in AlgType R TLim ilscaleAr.

End InvLimitAlg.
End InvLimitAlg.

Notation "[ 'algMixin' 'of' U 'by' <- ]" :=
  (InvLimitAlg.invlim_algMixin (Phant U))
  (at level 0, format "[ 'algMixin'  'of'  U  'by'  <- ]") : form_scope.


(*
Section InvLimitUnitAlg.

Variables (disp : unit) (I : porderType disp).
Variables (R : comUnitRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : invLimType Sys.

Canonical invlim_unitalgType := [unitAlgType R of TLim].

End InvLimitUnitAlg.
 *)


Module InvLimitField.
Section InvLimitField.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : comRingInvLimType Sys.

Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical invlim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].
Local Canonical TLim_idomainType :=
  Eval hnf in IdomainType TLim [idomainMixin of TLim by <-].

Fact invlim_fieldMixin of phant TLim :
  Field.mixin_of [unitRingType of TLim].
Proof.
move=> x /il_neq0 [i Hi].
apply/forallbP => j; rewrite unitfE.
have [k ilek jlek] := directedP i j.
have {Hi} : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
by rewrite -(ilprojE x jlek) fmorph_eq0.
Qed.
Local Canonical invlim_fieldType :=
  Eval hnf in FieldType TLim (invlim_fieldMixin (Phant TLim)).

End InvLimitField.
End InvLimitField.

Notation "[ 'fieldMixin' 'of' U 'by' <- ]" :=
  (InvLimitField.invlim_fieldMixin (Phant U))
  (at level 0, format "[ 'fieldMixin'  'of'  U  'by'  <- ]") : form_scope.

Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for inverse limits                            *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : invsys bonding.

Record invlim := InvLim {
                     invlimthr :> forall i, Ob i;
                     _ : `[<isthread Sys invlimthr>];
                   }.

Definition invlim_of of phantom (invsys bonding) Sys := invlim.
Identity Coercion type_invlim_of : invlim_of >-> invlim.

Local Notation "{ 'invlim' S }" := (invlim_of (Phantom _ S)).


Canonical invlim_eqType := EqType invlim gen_eqMixin.
Canonical invlimp_eqType := EqType {invlim Sys} gen_eqMixin.
Canonical invlim_choiceType := ChoiceType invlim gen_choiceMixin.
Canonical invlimp_choiceType := ChoiceType {invlim Sys} gen_choiceMixin.
Canonical invlimp_subType := [subType for invlimthr].

End Implem.
Notation "{ 'invlim' S }" := (invlim_of (Phantom _ S)).


Section InverseLimitTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.

Variable Sys : invsys bonding.
Implicit Type x y : {invlim Sys}.

Definition ilproj_impl i : {invlim Sys} -> Ob i :=
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

Variable (T : Type) (f : forall i, T -> Ob i).
Hypothesis Hcone : cone Sys f.

Definition ilind_impl t := InvLim (asboolT (cone_thr Hcone t)).
Lemma ilind_implP i t : 'pi_i (ilind_impl t) = f i t.
Proof. by []. Qed.

Lemma ilind_implE (un : T -> invlim Sys) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 ilind_impl.
Proof.
move=> H x; apply invlimP => i.
by rewrite -/(('pi_i \o un) _) H ilind_implP.
Qed.

End UniversalProperty.

End InverseLimitTheory.


Section InterSpec.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.
Variable Sys : invsys bonding.

Program Definition invlim_Mixin :=
  @InvLimMixin disp I Ob bonding Sys {invlim Sys}
               (ilproj_impl (Sys := Sys)) (ilind_impl (Sys := Sys)) _ _ _.
Next Obligation. by move=> i j Hij x; apply: ilproj_implE. Qed.
Next Obligation. by move=> x; apply: (ilind_implE Hcone). Qed.
Canonical invlim_invlimType := InvLimType {invlim Sys} invlim_Mixin.

End InterSpec.

Open Scope ring_scope.

Section Zmodule.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_zmodType :=
  Eval hnf in ZmodType {invlim Sys} [zmodMixin of {invlim Sys} by <-].
Canonical invlim_zmodInvlimType :=
  Eval hnf in ZmodInvLimType {invlim Sys} [zmodInvLimMixin of {invlim Sys} by <-].
End Zmodule.

Section Ring.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_ringType :=
  Eval hnf in RingType {invlim Sys} [ringMixin of {invlim Sys} by <-].
Canonical invlim_ringInvlimType :=
  Eval hnf in RingInvLimType {invlim Sys} [ringInvLimMixin of {invlim Sys} by <-].
End Ring.

Section ComRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_comRingType :=
  Eval hnf in ComRingType {invlim Sys} [comRingMixin of {invlim Sys} by <-].
Canonical invlim_comRingInvlimType :=
  Eval hnf in ComRingInvLimType {invlim Sys}.
End ComRing.

Section UnitRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_unitRingType :=
  Eval hnf in UnitRingType {invlim Sys} [unitRingMixin of {invlim Sys} by <-].
End UnitRing.

Section ComUnitRing.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_comUnitRingType := [comUnitRingType of {invlim Sys}].
End ComUnitRing.

Section Linear.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_lmodType :=
  Eval hnf in LmodType R {invlim Sys} [lmodMixin of {invlim Sys} by <-].
Canonical invlim_lmodInvLimType :=
  Eval hnf in LmodInvLimType R {invlim Sys} [lmodInvLimMixin of {invlim Sys} by <-].
End Linear.

Section Lalg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_lalgType :=
  Eval hnf in LalgType R {invlim Sys} [lalgMixin of {invlim Sys} by <-].
Canonical invlim_lalgInvLimType :=
  Eval hnf in LalgInvLimType R {invlim Sys}.
End Lalg.

Section Alg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_algType :=
  Eval hnf in AlgType R {invlim Sys} [algMixin of {invlim Sys} by <-].
End Alg.

Section UnitAlg.
Variables (disp : Datatypes.unit) (I : porderType disp).
Variables (R : comRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_unitAlgType := [unitAlgType R of {invlim Sys}].
End UnitAlg.

Section IDomain.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Canonical invlim_idomainType :=
  Eval hnf in IdomainType {invlim Sys} [idomainMixin of {invlim Sys} by <-].
End IDomain.

Section Field.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Canonical invlim_fieldType :=
  Eval hnf in FieldType {invlim Sys} [fieldMixin of {invlim Sys} by <-].
End Field.


Section TestAlg.
Variable (R : comRingType).
Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Let test := [algType R of {invlim Sys}].
End TestAlg.

Section TestField.
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Let test := [fieldType of {invlim Sys}].
End TestField.


(***************************************************************************)
(** Valuation in inverse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Ob : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%O -> {additive Ob j -> Ob i}.
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

Lemma lt_valuatP x n : reflect ('pi_n x = 0) (Nat n < valuat x)%O.
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
  reflect (forall i, (i < n)%N -> 'pi_i x = 0) (Nat n <= valuat x)%O.
Proof.
apply (iffP idP).
- case: valuatP => [v Hv vmin /= |-> _ i _].
  + by rewrite leEnatbar => nlev i /leq_trans/(_ nlev); apply vmin.
  + by rewrite raddf0.
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
by apply/invlimE=> i; rewrite raddf0; apply/lt_valuatP; rewrite valx.
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
  move=> Hlog; case (leP (valuat x1) (valuat x2)) => [|/ltW]/Hlog //.
  by rewrite addrC meetC.
rewrite (meet_idPl v1lev2); move: v1lev2.
case: (valuatP x1)=> [v1 Hv1 v1min|->]; last by rewrite add0r.
case: (valuatP x2)=> [v2 Hv2 v2min|->]; last by rewrite addr0 (valuatNatE Hv1).
rewrite leEnatbar => le12.
apply/le_valuatP => i Hi; rewrite raddfD /= v1min ?v2min ?addr0 //.
exact: leq_trans Hi le12.
Qed.
Lemma valuat_sum I r P (F : I ->  TLim) :
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

Section ValuationRing.

Variable Ob : nat -> ringType.
Variable bonding : forall i j : nat, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.

Variable TLim : ringInvLimType Sys.
Implicit Type (x y : TLim).

Lemma valuat1 : valuat (1 : TLim) = Nat 0.
Proof. by apply valuatNatE => [|i //]; rewrite rmorph1 oner_neq0. Qed.

End ValuationRing.


Section CommHugeOp.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j : I, (i <= j)%O -> Ob j -> Ob i.
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
  (i <= j)%O -> (ilopand sm i `<=` ilopand sm j)%fset.
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
    by case asboolP; rewrite {1}/invar => H s1 //; rewrite -Monoid.mulmA H.
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
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : invsys bonding.
Variable TLim : zmodInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> TLim.
Implicit Types (s x y z t : TLim).

Local Notation add_law := (add_comoid [zmodType of TLim]).

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
  (i <= j)%O -> (summand sm i `<=` summand sm j)%fset.
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
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob j -> Ob i}.
Variable Sys : invsys bonding.
Variable TLim : comRingInvLimType Sys.

Variable (C : choiceType).

Implicit Type F : C -> TLim.
Implicit Types (s x y z t : TLim).

Local Notation mul_law := (mul_comoid [comRingType of TLim]).

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
  (i <= j)%O -> (prodand sm i `<=` prodand sm j)%fset.
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
