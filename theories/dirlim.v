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
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar directed.


Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'dirlim' S }"
         (at level 0, format "{ 'dirlim'  S }").
Reserved Notation "''inj_' i" (at level 8, i at level 2, format "''inj_' i").



(***************************************************************************)
(** Direct systems and direct limits                                       *)
(*                                                                         *)
(***************************************************************************)
Section DirectSystem.

Variables (disp : unit) (I : dirType disp).

(** Objects and bonding morphisms of the direct system at left outside     *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Ob : I -> Type.
Variable bonding : (forall i j, i <= j -> Ob i -> Ob j).
Record dirsys : Type := DirSys {
      dirsys_inh : I;
      dirsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      dirsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hjk) \o (bonding Hij) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition dirsys_obj of dirsys := Ob.
Definition dirsys_mor of dirsys := bonding.

(* Is cocone *)
Definition iscompat of dirsys := fun T (mors : forall i, Ob i -> T) =>
  forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

(* Is section ? *)
Definition isthread of dirsys :=
  fun thr : forall i, option (Ob i) =>
    forall i j, forall (Hij : i <= j),
        if thr i is Some x then 
                                       bonding Hij (thr i) = thr j.
(* Is cocone *)
Definition iscompat of dirsys := fun T (mors : forall i, Ob i -> T) =>
  forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

End DirectSystem.



(***************************************************************************)
(** Interface for direct limits                                            *)
(*                                                                         *)
(***************************************************************************)
Module DirLim.

Section ClassDefs.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Record mixin_of (Tdir : Type) := Mixin {
  dirlim_inj : forall i, Ob i -> Tdir;
  dirlim_ind : forall (T : Type) (f : forall i, Ob i -> T),
      (iscompat Sys f) -> Tdir -> T;
  _ : iscompat Sys dirlim_inj;
  _ : forall T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f),
      forall i, dirlim_ind Hcomp \o @dirlim_inj i =1 f i;
  _ : forall T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f),
      forall (ind : Tdir -> T),
        (forall i, ind \o @dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind Hcomp
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
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation dirLimType := type.
Notation DirLimMixin := Mixin.

Section InternalTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.
Variable ilT : dirLimType Sys.

Definition inj_phant of phant ilT := dirlim_inj (mixin (class ilT)).
Local Notation "\inj" := (@inj_phant (Phant ilT)).
Local Notation "\inj_ i" := (@inj_phant (Phant ilT) i) (at level 5).
Definition ind_phant of phant ilT := dirlim_ind (mixin (class ilT)).
Local Notation "\ind" := (ind_phant (Phant ilT)).

Lemma inj_compat : iscompat Sys \inj.
Proof. by rewrite /inj_phant; case: ilT => /= [Tdir [eqM []]]. Qed.

Lemma ind_commute T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) :
  forall i, \ind Hcomp \o \inj_ i =1 f i.
Proof. by rewrite /inj_phant /ind_phant; case: ilT => /= [Tdir [eqM []]]. Qed.

Lemma piindE  T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) i x :
  (\ind Hcomp) (\inj_ i x) = f i x.
Proof. exact: ind_commute. Qed.

Lemma ind_uniq T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) :
  forall (ind : ilT -> T),
    (forall i, ind \o \inj_ i =1 f i) -> ind =1 \ind Hcomp.
Proof.
rewrite /inj_phant /ind_phant.
case: ilT => /= [Tdir [eqM /= [pi ind comp comm uniq]]] indT commT t /=.
by apply uniq; apply commT.
Qed.

End InternalTheory.

End Exports.
End DirLim.
Export DirLim.Exports.

Notation DirLimType T m := (@DirLim.pack _ _ _ _ _ T m _ _ id).
Notation "[ 'dirLimType' 'of' T 'for' cT ]" :=
  (@DirLim.clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'dirLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'dirLimType' 'of' T ]" :=
  (@DirLim.clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'dirLimType'  'of'  T ]") : form_scope.

Notation "''inj_' i" := (@inj_phant _ _ _ _ _ _ (Phant _) i).
Notation "''inj[' T ']_' i" := (@inj_phant _ _ _ _ _ _ (Phant T) i)
                              (at level 8, i at level 2, only parsing).
Notation "\ind" := (ind_phant (Phant _)).


Section Theory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.
Variable ilT : dirLimType Sys.

Lemma dirlimE (x y : ilT) : (forall i, 'inj_i x = 'inj_i y) -> x = y.
Proof.
move=> Heq.
pose fx : forall i : I, unit -> Ob i := fun i tt => 'pi_i x.
have compf : iscompat Sys fx.
  rewrite /fx => i j le_ij tt /=.
  by rewrite -/((bonding le_ij \o 'pi_j) x) proj_compat.
pose ind z : unit -> ilT := fun tt => z.
have Huniqy : forall i, 'pi_i \o ind y =1 fx i.
  by move=> i tt /=; rewrite /ind /fx Heq.
have Huniqx : forall i, 'pi_i \o ind x =1 fx i.
  by move=> i tt /=; rewrite /ind /fx Heq.
move: (ind_uniq compf Huniqx tt) (ind_uniq compf Huniqy tt).
by rewrite /ind /ind_phant => -> ->.
Qed.

Lemma from_thread_spec (thr : forall i : I, Ob i) :
  isthread Sys thr -> { t : ilT | forall i, 'pi_i t = thr i }.
Proof.
rewrite /isthread => Hhtr.
pose f : forall i : I, unit -> Ob i := fun i tt => thr i.
have compf : iscompat Sys f by rewrite /f => i j le_ij tt /=.
exists (\ind compf tt) => i.
by rewrite -/(('pi_i \o \ind compf) tt) ind_commute.
Qed.
Definition ilthr thr (Hthr : isthread Sys thr) :=
  let: exist res _ := from_thread_spec Hthr in res.

Lemma dirLimP thr (Hthr : isthread Sys thr) :
  forall i, 'pi_i (ilthr Hthr) = thr i.
Proof. by rewrite /ilthr; case: from_thread_spec. Qed.

Lemma ilprojE (x : ilT) :
  forall i j, forall (Hij : i <= j), bonding Hij ('pi_j x) = 'pi_i x.
Proof. by move=> i j Hij; have /= -> := (proj_compat Hij x). Qed.

Lemma ilprojP : iscompat Sys (pi_phant (ilT := ilT) (Phant _)).
Proof. move=> i j Hij x /=; exact: ilprojE. Qed.

Lemma dirlim_exE (x y : ilT) :
  (forall i, exists2 i0, i0 >= i & 'pi_i0 x = 'pi_i0 y) -> x = y.
Proof.
move=> Heq; apply dirlimE => i.
have:= Heq i => [][i0 le_ii0] /(congr1 (bonding le_ii0)).
by rewrite !ilprojE.
Qed.

Lemma dirlim_geE b (x y : ilT) :
  (forall i, i >= b -> 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> Heq; apply dirlim_exE => i.
by have:= directedP i b => [][j le_ij {}/Heq Heq]; exists j.
Qed.

End Theory.
Arguments ilthr {disp I Ob bonding Sys ilT thr}.
Arguments dirlim_geE {disp I Ob bonding Sys ilT}.


(****************************************************************************)
(** Direrse limits in various algebraic categories                          *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)
Open Scope ring_scope.
Import GRing.Theory.

Section DirLimitEqType.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.

Variable Sys : dirsys bonding.
Variable T : dirLimType Sys.
Implicit Type x y : T.

Lemma dirlimPn x y : reflect (exists i, 'pi_i x != 'pi_i y) (x != y).
Proof.
apply (iffP idP) => [neq|[i]]; last by apply/contra => /eqP ->.
apply/asboolP; rewrite asbool_existsNb; apply/contra: neq => /asboolP Hx.
by apply/eqP/dirlimE => /= i; apply/eqP.
Qed.

End DirLimitEqType.


Module DirLimitZMod.
Section DirLimitZMod.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type x y : Tdir.

Fact ilzeroP : isthread Sys (fun i => 0 : Ob i).
Proof. by move=> i j Hij; rewrite raddf0. Qed.
Definition ilzero : Tdir := ilthr ilzeroP.

Fact iloppP x : isthread Sys (fun i => - ('pi_i x)).
Proof. by move=> i j Hij; rewrite raddfN (ilprojE x). Qed.
Definition ilopp x : Tdir := ilthr (iloppP x).

Fact iladdP x y : isthread Sys (fun i => 'pi_i x + 'pi_i y).
Proof. by move=> i j Hij; rewrite raddfD (ilprojE x) (ilprojE y). Qed.
Definition iladd x y : Tdir := ilthr (iladdP x y).

Program Definition dirlim_zmodMixin of phant Tdir :=
  @ZmodMixin Tdir ilzero ilopp iladd _ _ _ _.
Next Obligation. by move=> a b c; apply dirlimE=> i; rewrite !dirLimP addrA. Qed.
Next Obligation. by move=> a b; apply dirlimE=> i; rewrite !dirLimP addrC. Qed.
Next Obligation. by move=> b; apply dirlimE=> i; rewrite !dirLimP add0r. Qed.
Next Obligation. by move=> b; apply dirlimE=> i; rewrite !dirLimP addNr. Qed.
(* Not global canonical but accessible by [zmodMixin of ... by <-] *)
(* A mettre dans un module pour avoir le canonical local *)

Local Canonical dirlim_zmodType :=
  Eval hnf in ZmodType Tdir (dirlim_zmodMixin (Phant Tdir)).

Fact ilproj_is_additive i : additive 'pi_i.
Proof. by move=> x y; rewrite !dirLimP. Qed.
Canonical ilproj_additive i : {additive Tdir -> Ob i} :=
  Additive (ilproj_is_additive i).

Lemma il_neq0 x : x != 0 -> exists i, 'pi_i x != 0.
Proof. by move/dirlimPn=> [i]; rewrite raddf0 => Hi; exists i. Qed.

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_is_additive : additive (\ind Hcomp).
Proof.
by move=> t u; apply dirlimE=> i; rewrite raddfB /= !piindE raddfB.
Qed.
Canonical ilind_additive : {additive T -> Tdir} :=
  Additive ilind_is_additive.

End UniversalProperty.

End DirLimitZMod.
End DirLimitZMod.

Definition il_neq0 := DirLimitZMod.il_neq0.
Notation "[ 'zmodMixin' 'of' U 'by' <- ]" :=
  (DirLimitZMod.dirlim_zmodMixin (Phant U))
  (at level 0, format "[ 'zmodMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical ilproj_additive := DirLimitZMod.ilproj_additive.
Canonical ilind_additive := DirLimitZMod.ilind_additive.


Module DirLimitRing.
Section DirLimitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type x y : Tdir.

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].

Fact iloneP : isthread Sys (fun i => 1 : Ob i).
Proof. by move=> i j Hij; rewrite rmorph1. Qed.
Definition ilone : Tdir := ilthr iloneP.

Fact ilmulP x y : isthread Sys (fun i => 'pi_i x * 'pi_i y).
Proof. by move=> i j Hij; rewrite rmorphM (ilprojE x) (ilprojE y). Qed.
Definition ilmul x y : Tdir := ilthr (ilmulP x y).

Program Definition dirlim_ringMixin of phant Tdir :=
  @RingMixin _ ilone ilmul _ _ _ _ _ _.
Next Obligation. by move=> a b c; apply dirlimE=> i; rewrite !dirLimP mulrA. Qed.
Next Obligation. by move=> a; apply dirlimE=> i; rewrite !dirLimP mul1r. Qed.
Next Obligation. by move=> a; apply dirlimE=> i; rewrite !dirLimP mulr1. Qed.
Next Obligation. by move=> a b c; apply dirlimE=> i; rewrite !dirLimP mulrDl. Qed.
Next Obligation. by move=> a b c; apply dirlimE=> i; rewrite !dirLimP mulrDr. Qed.
Next Obligation.
apply/negP => /eqP/(congr1 (fun x => 'pi_(dirsys_inh Sys) x)) /= /eqP.
by rewrite !dirLimP; exact/negP/oner_neq0.
Qed.
Local Canonical dirlim_ringType :=
  Eval hnf in RingType Tdir (dirlim_ringMixin (Phant Tdir)).

Fact ilproj_is_multiplicative i : multiplicative 'pi_i.
Proof. by split => [x y|]; rewrite !dirLimP. Qed.
Canonical ilproj_rmorphism i : {rmorphism Tdir -> Ob i} :=
  AddRMorphism (ilproj_is_multiplicative i).

Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_is_multiplicative : multiplicative (\ind Hcomp).
Proof.
split.
- by move=> t u; apply dirlimE=> i; rewrite !piindE !rmorphM /= !piindE.
- by apply dirlimE=> i; rewrite piindE !rmorph1.
Qed.
Canonical ilind_rmorphism : {rmorphism T -> Tdir} :=
  AddRMorphism ilind_is_multiplicative.

End UniversalProperty.

End DirLimitRing.
End DirLimitRing.

Notation "[ 'ringMixin' 'of' U 'by' <- ]" :=
  (DirLimitRing.dirlim_ringMixin (Phant U))
  (at level 0, format "[ 'ringMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical ilproj_multiplicative := DirLimitRing.ilproj_rmorphism.
Canonical ilind_multiplicative := DirLimitRing.ilind_rmorphism.


Module DirLimitComRing.
Section DirLimitComRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type x y : Tdir.

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].

Fact ilmulC x y : x * y = y * x.
Proof. by apply dirlimE=> i; rewrite !dirLimP mulrC. Qed.
Definition dirlim_comRingMixin of phant Tdir := ilmulC.

End DirLimitComRing.
End DirLimitComRing.

Notation "[ 'comRingMixin' 'of' U 'by' <- ]" :=
  (DirLimitComRing.dirlim_comRingMixin (Phant U))
  (at level 0, format "[ 'comRingMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitUnitRing.
Section DirLimitUnitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type x y : Tdir.

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].

Definition ilunit x := `[forall i, 'pi_i x \is a GRing.unit].

Fact dir_isunitP x :
  (forall i, 'pi_i x \is a GRing.unit) -> isthread Sys (fun i => ('pi_i x)^-1).
Proof.
by move=> Hunit i j ilej; rewrite /= rmorphV ?(ilprojE x) // Hunit.
Qed.
Definition ildir x : Tdir :=
  if pselect (forall i, 'pi_i x \is a GRing.unit) is left Pf
  then ilthr (dir_isunitP Pf) else x.


Fact ilmulVr : {in ilunit, left_direrse 1 ildir *%R}.
Proof.
move=> x /forallbP Hdir; apply dirlimE=> i.
rewrite /ildir; case: pselect => /= [H |/(_ Hdir)//].
by rewrite !dirLimP mulVr // Hdir.
Qed.
Fact ilmulrV : {in ilunit, right_direrse 1 ildir *%R}.
Proof.
move=> x /forallbP Hdir; apply dirlimE=> i.
rewrite /ildir; case: pselect => /= [H |/(_ Hdir)//].
by rewrite !dirLimP mulrV // Hdir.
Qed.
Fact ilunit_impl x y : y * x = 1 /\ x * y = 1 -> ilunit x.
Proof.
move=> [Hxy Hyx]; apply/forallbP => i; apply/unitrP.
by exists ('pi_i y); rewrite -!rmorphM Hxy Hyx /= rmorph1.
Qed.
Fact ildir0id : {in [predC ilunit], ildir =1 id}.
Proof.
move=> x; rewrite inE /= => /forallbP Hx.
by rewrite /ildir; case: pselect => /= [/= H|//]; have:= Hx H.
Qed.
Definition dirlim_unitRingMixin of (phant Tdir) :=
  Eval hnf in UnitRingMixin ilmulVr ilmulrV ilunit_impl ildir0id.
Local Canonical Tdir_unitRingType :=
  Eval hnf in UnitRingType Tdir (dirlim_unitRingMixin (Phant Tdir)).

Lemma ilunitP x :
  reflect (forall i, 'pi_i x \is a GRing.unit) (x \is a GRing.unit).
Proof. exact: forallbP. Qed.

End DirLimitUnitRing.
End DirLimitUnitRing.

Notation "[ 'unitRingMixin' 'of' U 'by' <- ]" :=
  (DirLimitUnitRing.dirlim_unitRingMixin (Phant U))
  (at level 0, format "[ 'unitRingMixin'  'of'  U  'by'  <- ]") : form_scope.

Definition ilunitP := DirLimitUnitRing.ilunitP.

(** No more useful
Section DirLimitComUnitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].
Local Canonical Tdir_unitRingType :=
  Eval hnf in UnitRingType Tdir [unitRingMixin of Tdir by <-].
Local Canonical Tdir_comRingType :=
  Eval hnf in ComRingType Tdir [comRingMixin of Tdir by <-].
Local Canonical dirlim_comUnitRingType := Eval hnf in [comUnitRingType of Tdir].

End DirLimitComUnitRing.
*)


Module DirLimitIDomain.
Section DirLimitIDomain.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type (x y : Tdir).

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].
Local Canonical Tdir_unitRingType :=
  Eval hnf in UnitRingType Tdir [unitRingMixin of Tdir by <-].
Local Canonical Tdir_comRingType :=
  Eval hnf in ComRingType Tdir [comRingMixin of Tdir by <-].
Local Canonical Tdir_comUnitRingType := Eval hnf in [comUnitRingType of Tdir].

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

Definition dirlim_idomainMixin of phant Tdir := ilmul_eq0.

End DirLimitIDomain.
End DirLimitIDomain.

Notation "[ 'idomainMixin' 'of' U 'by' <- ]" :=
  (DirLimitIDomain.dirlim_idomainMixin (Phant U))
  (at level 0, format "[ 'idomainMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitLinear.
Section DirLimitLinear.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type (x y : Tdir) (r : R).

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].

Fact ilscaleP r x : isthread Sys (fun i => r *: 'pi_i x).
Proof. by move=> i j Hij; rewrite linearZ (ilprojE x). Qed.
Definition ilscale r x : Tdir := ilthr (ilscaleP r x).

Program Definition dirlim_lmodMixin of phant Tdir :=
  @LmodMixin R [zmodType of Tdir] ilscale _ _ _ _.
Next Obligation. by apply dirlimE=> i /=; rewrite !dirLimP scalerA. Qed.
Next Obligation. by move=> x; apply dirlimE=> i; rewrite !dirLimP scale1r. Qed.
Next Obligation. by move=> r x y; apply dirlimE=> i; rewrite !dirLimP scalerDr. Qed.
Next Obligation. by move=> r s; apply dirlimE=> i; rewrite !dirLimP scalerDl. Qed.

Local Canonical dirlim_lmodType :=
  Eval hnf in LmodType R Tdir (dirlim_lmodMixin (Phant Tdir)).

Fact ilproj_is_linear i : linear 'pi_i.
Proof. by move=> c x y; rewrite !dirLimP. Qed.
Canonical ilproj_linear i : {linear Tdir -> Ob i} :=
  AddLinear (ilproj_is_linear i).

Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_is_linear : linear (\ind Hcomp).
Proof.
by move=> r t u; apply dirlimE=> i; rewrite !dirLimP !piindE !linearP.
Qed.
Canonical ilind_linear : {linear T -> Tdir} := AddLinear ilind_is_linear.

End UniversalProperty.

End DirLimitLinear.
End DirLimitLinear.

Notation "[ 'lmodMixin' 'of' U 'by' <- ]" :=
  (DirLimitLinear.dirlim_lmodMixin (Phant U))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical ilproj_linear := DirLimitLinear.ilproj_linear.
Canonical ilind_linear := DirLimitLinear.ilind_linear.


Module DirLimitLalg.
Section DirLimitLalg.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type (x y : Tdir) (r : R).

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].
Local Canonical Tdir_lmodType :=
  Eval hnf in LmodType R Tdir [lmodMixin of Tdir by <-].

Fact ilscaleAl r x y : r *: (x * y) = r *: x * y.
Proof. by apply dirlimE=> i /=; rewrite !dirLimP scalerAl. Qed.
Definition dirlim_lalgMixin of phant Tdir := ilscaleAl.
Local Canonical dirlim_lalgType := Eval hnf in LalgType R Tdir ilscaleAl.

Canonical ilproj_lrmorphism i : {lrmorphism Tdir -> Ob i} :=
  AddLRMorphism (DirLimitLinear.ilproj_is_linear i).

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism T -> (Ob i)}).
Hypothesis Hcomp : iscompat Sys f.
Canonical ilind_lrmorphism : {lrmorphism T -> Tdir} :=
  AddLRMorphism (DirLimitLinear.ilind_is_linear Tdir Hcomp).

End UniversalProperty.

End DirLimitLalg.
End DirLimitLalg.

Notation "[ 'lalgMixin' 'of' U 'by' <- ]" :=
  (DirLimitLalg.dirlim_lalgMixin (Phant U))
  (at level 0, format "[ 'lalgMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical ilproj_lrmorphism := DirLimitLalg.ilproj_lrmorphism.
Canonical ilind_lrmorphism := DirLimitLalg.ilind_lrmorphism.


Module DirLimitAlg.
Section DirLimitAlg.

Variables (disp : unit) (I : dirType disp).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.
Implicit Type (x y : Tdir) (r : R).

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].
Local Canonical Tdir_lmodType :=
  Eval hnf in LmodType R Tdir [lmodMixin of Tdir by <-].
Local Canonical dirlim_lalgType :=
  Eval hnf in LalgType R Tdir [lalgMixin of Tdir by <-].

Fact ilscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof. by apply dirlimE=> i /=; rewrite !dirLimP scalerAr. Qed.
Definition dirlim_algMixin of phant Tdir := ilscaleAr.
Canonical dirlim_algType := Eval hnf in AlgType R Tdir ilscaleAr.

End DirLimitAlg.
End DirLimitAlg.

Notation "[ 'algMixin' 'of' U 'by' <- ]" :=
  (DirLimitAlg.dirlim_algMixin (Phant U))
  (at level 0, format "[ 'algMixin'  'of'  U  'by'  <- ]") : form_scope.


(*
Section DirLimitUnitAlg.

Variables (disp : unit) (I : dirType disp).
Variables (R : comUnitRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.

Canonical dirlim_unitalgType := [unitAlgType R of Tdir].

End DirLimitUnitAlg.
 *)


Module DirLimitField.
Section DirLimitField.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Variable Tdir : dirLimType Sys.

Local Canonical Tdir_zmodType :=
  Eval hnf in ZmodType Tdir [zmodMixin of Tdir by <-].
Local Canonical Tdir_ringType :=
  Eval hnf in RingType Tdir [ringMixin of Tdir by <-].
Local Canonical Tdir_unitRingType :=
  Eval hnf in UnitRingType Tdir [unitRingMixin of Tdir by <-].
Local Canonical Tdir_comRingType :=
  Eval hnf in ComRingType Tdir [comRingMixin of Tdir by <-].
Local Canonical dirlim_comUnitRingType := Eval hnf in [comUnitRingType of Tdir].
Local Canonical Tdir_idomainType :=
  Eval hnf in IdomainType Tdir [idomainMixin of Tdir by <-].

Fact dirlim_fieldMixin of phant Tdir :
  GRing.Field.mixin_of [unitRingType of Tdir].
Proof.
move=> x /il_neq0 [i Hi].
apply/forallbP => j; rewrite unitfE.
have [k ilek jlek] := directedP i j.
have {Hi} : 'pi_k x != 0.
  move: Hi; apply contra => /eqP/(congr1 (bonding ilek)).
  by rewrite (ilprojE x) raddf0 => ->.
by rewrite -(ilprojE x jlek) fmorph_eq0.
Qed.

End DirLimitField.
End DirLimitField.

Notation "[ 'fieldMixin' 'of' U 'by' <- ]" :=
  (DirLimitField.dirlim_fieldMixin (Phant U))
  (at level 0, format "[ 'fieldMixin'  'of'  U  'by'  <- ]") : form_scope.

Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for direrse limits                            *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.
Variable Sys : dirsys bonding.

Record dirlim := DirLim {
                     dirlimthr :> forall i, Ob i;
                     _ : `[<isthread Sys dirlimthr>];
                   }.

Definition dirlim_of of phantom (dirsys bonding) Sys := dirlim.
Identity Coercion type_dirlim_of : dirlim_of >-> dirlim.

Local Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).


Canonical dirlim_eqType := EqType dirlim gen_eqMixin.
Canonical dirlimp_eqType := EqType {dirlim Sys} gen_eqMixin.
Canonical dirlim_choiceType := ChoiceType dirlim gen_choiceMixin.
Canonical dirlimp_choiceType := ChoiceType {dirlim Sys} gen_choiceMixin.
Canonical dirlimp_subType := [subType for dirlimthr].

Definition MkDirLim thr (thrP : isthread Sys thr) := DirLim (asboolT thrP).
Lemma MkDirLimE thr (thrP : isthread Sys thr) :
  val (MkDirLim thrP) = thr.
Proof. by []. Qed.

End Implem.
Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).


Section DirerseLimitTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob j -> Ob i.

Variable Sys : dirsys bonding.
Implicit Type x y : {dirlim Sys}.

Definition ilproj_impl i : {dirlim Sys} -> Ob i :=
  (dirlimthr (Sys := Sys))^~ i.

Lemma ilproj_implE x :
  forall i j, forall (Hij : i <= j),
      bonding Hij (ilproj_impl j x) = ilproj_impl i x.
Proof. by case: x => [thr /asboolP] /=. Qed.

Lemma ilproj_implP : iscompat Sys ilproj_impl.
Proof. by move=> i j Hij [thr /asboolP] /=. Qed.

Local Notation "''pi_' i" := (ilproj_impl i).

Lemma dirlimP x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> eqxy; apply val_inj => /=.
case: x y eqxy => [fx _] [fy _] /=.
exact: functional_extensionality_dep.
Qed.

(** Building the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Ob i -> T).
Hypothesis Hcomp : iscompat Sys f.

Fact ilind_spec :
  { ilind : T -> dirlim Sys | forall i, 'pi_i \o ilind = f i }.
Proof.
move: Hcomp; rewrite /iscompat => Hf; pose fil t i := f i t.
have Hfil t : isthread Sys (fil t) by rewrite /fil=> i j Hij; apply Hf.
by exists (fun t => MkDirLim (Hfil t)).
Qed.
Definition ilind_impl := let: exist f _ := ilind_spec in f.
Lemma ilind_implP i t : 'pi_i (ilind_impl t) = f i t.
Proof.
rewrite /ilind_impl; move: t; case: ilind_spec => un Hun t.
by rewrite -Hun.
Qed.

Lemma ilind_implE (un : T -> dirlim Sys) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 ilind_impl.
Proof.
move=> H x; apply dirlimP => i.
by rewrite -/(('pi_i \o un) _) H ilind_implP.
Qed.

End UniversalProperty.

End DirerseLimitTheory.


Section InterSpec.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.
Variable Sys : dirsys bonding.

Program Definition dirlim_Mixin :=
  @DirLimMixin disp I Ob bonding Sys {dirlim Sys}
               (ilproj_impl (Sys := Sys)) (ilind_impl (Sys := Sys)) _ _ _.
Next Obligation. by move=> i j Hij x; apply: ilproj_implE. Qed.
Next Obligation. by move=> x /=; rewrite ilind_implP. Qed.
Next Obligation. by move=> x; apply: (ilind_implE Hcomp). Qed.
Canonical dirlim_dirlimType := DirLimType {dirlim Sys} dirlim_Mixin.

End InterSpec.


Open Scope ring_scope.
Section Canonicals.

Variables (disp : unit) (I : dirType disp).

Section ZModule.
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : dirsys bonding.
Canonical dirlim_zmodType :=
  Eval hnf in ZmodType {dirlim Sys} [zmodMixin of {dirlim Sys} by <-].
End ZModule.

Section Ring.
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_ringType :=
  Eval hnf in RingType {dirlim Sys} [ringMixin of {dirlim Sys} by <-].
End Ring.

Section ComRing.
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_comRingType :=
  Eval hnf in ComRingType {dirlim Sys} [comRingMixin of {dirlim Sys} by <-].
End ComRing.

Section UnitRing.
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_unitRingType :=
  Eval hnf in UnitRingType {dirlim Sys} [unitRingMixin of {dirlim Sys} by <-].
End UnitRing.

Section ComUnitRing.
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlimp_comUnitRingType := [comUnitRingType of {dirlim Sys}].
End ComUnitRing.

Section IDomain.
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_idomainType :=
  Eval hnf in IdomainType {dirlim Sys} [idomainMixin of {dirlim Sys} by <-].
End IDomain.

Section Linear.
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_lmodType :=
  Eval hnf in LmodType R {dirlim Sys} [lmodMixin of {dirlim Sys} by <-].
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_lalgType :=
  Eval hnf in LalgType R {dirlim Sys} [lalgMixin of {dirlim Sys} by <-].
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_algType :=
  Eval hnf in AlgType R {dirlim Sys} [algMixin of {dirlim Sys} by <-].
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlimp_unitAlgType := [unitAlgType R of {dirlim Sys}].
End UnitAlg.

Section Field.
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_fieldType :=
  Eval hnf in FieldType {dirlim Sys} [fieldMixin of {dirlim Sys} by <-].
End Field.

End Canonicals.


Section Test.
Variable (R : comRingType).
Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : dirsys bonding.
Let test := [algType R of {dirlim Sys}].
End Test.


(***************************************************************************)
(** Valuation in direrse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Ob : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Implicit Type (x y : {dirlim Sys}).


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
by apply/dirlimE=> i; rewrite raddf0; apply/lt_valuatP; rewrite valx.
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
Lemma valuat_sum I r P (F : I ->  {dirlim Sys}) :
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

(*
From mathcomp Require Import finmap.

Section CommHugeOp.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j : I, (i <= j)%O -> (Ob j) -> (Ob i).
Variable Sys : dirsys bonding.

Variable (C : choiceType).
Variables (idx : {dirlim Sys}) (op : Monoid.com_law idx).

Implicit Type F : C -> {dirlim Sys}.
Implicit Types (x y z t : {dirlim Sys}).

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
apply/fsubsetP => c; apply/contraLR => /ilopableP Hdir.
by apply/ilopableP => x; rewrite -!(ilprojE _ ilej) Hdir.
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

Definition HugeOp F : {dirlim Sys} :=
  if pselect (is_ilopable F) is left sm
  then MkDirLim (ilopable_istrhead sm)
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
*)
