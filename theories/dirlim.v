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
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order bigop.

Require Import natbar directed.


Import GRing.
Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.


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

Variables (disp : Datatypes.unit) (I : porderType disp).

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

Lemma bondingE i j (Hij1 Hij2 : i <= j) : bonding Hij1 =1 bonding Hij2.
Proof. by rewrite (Prop_irrelevance Hij1 Hij2). Qed.

Lemma bonding_transE (Sys : dirsys) i j k (Hij : i <= j) (Hjk : j <= k) x :
  (bonding Hjk) (bonding Hij x) = bonding (le_trans Hij Hjk) x.
Proof. by move/dirsys_comp : Sys; apply. Qed.

Definition cocone of dirsys := fun T (mors : forall i, Ob i -> T) =>
  forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

Lemma coconeE Sys T (mors : forall i, Ob i -> T) : cocone Sys mors ->
  forall i j (Hij : i <= j) x,
  mors j (bonding Hij x) = mors i x.
Proof. by rewrite /cocone => H i j le_ij x; rewrite -(H i j le_ij). Qed.

End DirectSystem.



(***************************************************************************)
(** Interface for direct limits                                            *)
(*                                                                         *)
(***************************************************************************)
Open Scope ring_scope.


#[key="TLim"]
HB.mixin Record isDirLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : dirsys bonding)
  TLim of Choice TLim := {
    dirlim_inj : forall i, Obj i -> TLim;
    dirlim_ind : forall (T : Type) (f : forall i, Obj i -> T),
      (cocone Sys f) -> TLim -> T;
    dlinjP : cocone Sys dirlim_inj;
    dlind_commute : forall T (f : forall i, Obj i -> T) (Hcone : cocone Sys f),
      forall i, dirlim_ind T f Hcone \o dirlim_inj i =1 f i;
    dlind_uniq : forall T (f : forall i, Obj i -> T) (Hcone : cocone Sys f),
      forall (ind : TLim -> T),
        (forall i, ind \o dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind T f Hcone
  }.

#[short(type="dirLimType")]
HB.structure Definition DirLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : dirsys bonding)
  := {
    TLim of isDirLim disp I Obj bonding Sys TLim
    & Choice TLim
  }.



Section InternalTheory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.
Variable dlT : dirLimType Sys.

Definition inj_phant of phant dlT := (@dirlim_inj _ _ _ _ _ dlT).
Local Notation "\inj" := (@inj_phant (Phant dlT)).
Local Notation "\inj_ i" := (@inj_phant (Phant dlT) i) (at level 5).
Definition ind_phant of phant dlT := (@dirlim_ind _ _ _ _ _ dlT).
Local Notation "\ind" := (ind_phant (Phant dlT)).

Lemma dlinjE :
  forall i j, forall (Hij : i <= j) x, \inj_j (bonding Hij x) = \inj_i x.
Proof. by move=> i j Hij x; rewrite [LHS]dlinjP. Qed.

Lemma injindE  T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) i x :
  (\ind Hcone) (\inj_ i x) = f i x.
Proof. exact: dlind_commute. Qed.

End InternalTheory.

Arguments dlinjP {disp I Obj bonding} [Sys].

Notation "''inj[' TLim ']_' i" := (@inj_phant _ _ _ _ _ TLim (Phant _) i)
                              (at level 8, i at level 2, only parsing).
Notation "''inj[' TLim ']'" := ('inj[TLim]_ _) (at level 8).
Notation "''inj_' i" := ('inj[ _ ]_ i).
Notation "''inj'" := ('inj[ _ ]_ _).
Notation "''ind'" := (ind_phant (Phant _)).
Notation "''ind[' T ']'" := (ind_phant (Phant T)) (only parsing).


Section Theory.

Variables (disp : Datatypes.unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (u v w : TLim).

Inductive dirlim_spec u : Prop :=
  | DirLimSpec : forall k (x : Obj k), 'inj x = u -> dirlim_spec u.

Lemma dirlimP u : dirlim_spec u.
Proof.
suff: exists k (y : Obj k), 'inj y = u by case=> i [x <-{u}]; exists i x.
rewrite not_existsP => H.
pose f i := pred0 (T := Obj i).
have Hcone : cocone Sys f by [].
have /(dlind_uniq _ _ Hcone)/(_ u) :
  forall i, (pred0 (T := TLim)) \o 'inj =1 f i by [].
suff /(dlind_uniq _ _ Hcone)/(_ u) <- : forall i, (pred1 u) \o 'inj =1 f i.
  by rewrite /= eqxx.
rewrite /f => i x /=; apply/negP => /eqP eq_inj.
by apply/(H i); exists x.
Qed.

Lemma dirlimSP u : { p : {i & Obj i} | 'inj (projT2 p) = u }.
Proof.
by apply cid; case: (dirlimP u) => i x eqinj; exists (existT _ i x).
Qed.

End Theory.


Section DirLimDirected.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.
Variable TLim : dirLimType Sys.
Implicit Type (u v w : TLim).

Inductive dirlim2_spec u v : Prop :=
  | DirLim2Spec :
    forall k (x y : Obj k), 'inj x = u -> 'inj y = v
                            -> dirlim2_spec u v.
Inductive dirlim3_spec u v w : Prop :=
  | DirLim3Spec :
    forall k (x y z : Obj k), 'inj x = u -> 'inj y = v -> 'inj z = w
                              -> dirlim3_spec u v w.

Lemma dirlim2P u v : dirlim2_spec u v.
Proof.
case: (dirlimP u) => /= iu x <-{u}.
case: (dirlimP v) => /= iv y <-{v}.
case: (directedP iu iv) => n le_ian le_ibn.
by exists n (bonding le_ian x) (bonding le_ibn y); rewrite dlinjE.
Qed.
Lemma dirlimS2P u v :
  { p : {i & (Obj i * Obj i)%type} |
    'inj (projT2 p).1 = u /\ 'inj (projT2 p).2 = v }.
Proof.
apply cid; case: (dirlim2P u v) => i x y eqx eqy.
by exists (existT _ i (x, y)) => /=.
Qed.

Lemma dirlim3P u v w : dirlim3_spec u v w.
Proof.
case: (dirlim2P u v) => i x y <-{u} <-{v}.
case: (dirlimP w) => /= j z <-{w}.
case: (directedP i j) => n le_in le_jn.
by exists n (bonding le_in x) (bonding le_in y) (bonding le_jn z); rewrite dlinjE.
Qed.

End DirLimDirected.


Section DirSysCongr.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.

Implicit Types (i j k : I).

(* We use a inductive type for implicit argument *)
Inductive dsyscongr i j (x : Obj i) (y : Obj j) : Prop :=
  | Dsyscongr : forall k (le_ik : i <= k) (le_jk : j <= k),
              (bonding le_ik x = bonding le_jk y) -> dsyscongr x y.
Arguments Dsyscongr {i j x y k} (le_ik le_jk).

Lemma dsyscongr_bonding i j (le_ij : i <= j) (x : Obj i) :
  dsyscongr x (bonding le_ij x).
Proof.
apply: (Dsyscongr le_ij (lexx j)).
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dsyscongr_refl i (x : Obj i) : dsyscongr x x.
Proof. exact: Dsyscongr. Qed.
Lemma dsyscongr_sym_impl i j (x : Obj i) (y : Obj j) : dsyscongr x y -> dsyscongr y x.
Proof.
move=> [k le_ik le_jk Hbond].
by apply: (Dsyscongr le_jk le_ik); rewrite Hbond.
Qed.
Lemma dsyscongr_sym i j (x : Obj i) (y : Obj j) : dsyscongr x y = dsyscongr y x.
Proof. by rewrite propeqE; split; apply: dsyscongr_sym_impl. Qed.
Lemma dsyscongr_trans i j k (x : Obj i) (y : Obj j) (z : Obj k) :
  dsyscongr x y -> dsyscongr y z -> dsyscongr x z.
Proof.
move=> [l le_il le_jl Hxy].
move=> [m le_jm le_km Hyz].
have [n le_ln le_mn] := directedP l m.
apply: (Dsyscongr (le_trans le_il le_ln) (le_trans le_km le_mn)).
rewrite -!bonding_transE // {}Hxy -{}Hyz !bonding_transE //.
exact: bondingE.
Qed.

Lemma cocone_dsyscongr i (x : Obj i) :
  cocone Sys (fun j (y : Obj j) => `[< dsyscongr x y >]).
Proof.
move=> j k le_jk y /=.
case: (boolP `[< dsyscongr x y >]) => [Hthr | Hnthr].
- move: Hthr => /asboolP [l le_il le_jl Hbond]; apply/asboolP.
  have [m le_km le_lm] := directedP k l.
  apply: (Dsyscongr (le_trans le_il le_lm) le_km).
  rewrite -(dirsys_comp Sys le_il le_lm) /= Hbond.
  by rewrite !bonding_transE //; apply: bondingE.
- apply/negP => /= /asboolP [l le_il le_kl].
  rewrite bonding_transE // => Hbond.
  move: Hnthr => /asboolP; apply.
  exact: (Dsyscongr le_il (le_trans le_jk le_kl)).
Qed.

Section Compatibility.

Variables (T : Type) (f : forall i, Obj i -> T).
Hypothesis Hcone : cocone Sys f.

Lemma dsyscongrE i j (x : Obj i) (y : Obj j) : dsyscongr x y -> f x = f y.
Proof.
move=> [k le_ik le_jk Hbond].
by rewrite -(coconeE Hcone le_ik) Hbond (coconeE Hcone).
Qed.

End Compatibility.

End DirSysCongr.
Arguments Dsyscongr {disp I Obj bonding i j x y k} (le_ik le_jk).


Section DirLimitEqType.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> eqType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.
Variable TLim : dirLimType Sys.
Implicit Type (u v w : TLim).

Lemma dirlimE i j (x : Obj i) (y : Obj j) :
  (exists k (leik : i <= k) (lejk : j <= k), bonding leik x = bonding lejk y)
  <->
  ('inj[TLim] x = 'inj[TLim] y).
Proof.
split=> [[k][leik][lejk]/(congr1 'inj[TLim]) | eqinj]; first by rewrite !dlinjE.
apply contrapT; rewrite -forallNP => Hbond.
have Hcone := cocone_dsyscongr Sys y.
have:= injindE TLim Hcone y; rewrite -eqinj injindE.
have /asboolP -> := dsyscongr_refl bonding y.
move=> /asboolP [k le_jk le_ik] Habs.
apply: (Hbond k); exists (le_ik); exists (le_jk); rewrite Habs.
exact: bondingE.
Qed.

End DirLimitEqType.


(****************************************************************************)
(**  Interface for inverse limits in various algebraic categories           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

#[key="TLim"]
HB.mixin Record isZmoduleDirLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j : I, i <= j -> {additive Obj i -> Obj j})
    (Sys : dirsys bonding)
    (TLim : Type) of DirLim disp Sys TLim & Zmodule TLim := {
  dlinj_is_additive :
    forall i : I, additive 'inj[TLim]_i
  }.

#[short(type="zmodDirLimType")]
HB.structure Definition ZmodDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of DirLim disp Sys TLim
    & isZmoduleDirLim disp I Obj bonding Sys TLim
    & Zmodule TLim
  }.

Section ZmodDirLimTheory.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> zmodType.
Variable bonding : forall i j, i <= j -> {additive Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Variable TLim : zmodDirLimType Sys.
Implicit Type x y : TLim.

HB.instance Definition _ i :=
  isAdditive.Build (Obj i) TLim _ (dlinj_is_additive i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_additive : additive ('ind[TLim] Hcone).
Proof.
move=> /= u v; case: (dirlim2P u v) => i x y <-{u} <-{v}.
by rewrite -raddfB /= !injindE raddfB.
Qed.
HB.instance Definition _ :=
  isAdditive.Build TLim T _ dlind_is_additive.

End UniversalProperty.

Lemma dl_eq0 x : x = 0 -> exists i, 'inj[TLim]_i 0 = x.
Proof.
case: (dirlimP x) => i y <-{x} eqinj; exists i.
by rewrite {}eqinj raddf0.
Qed.

Lemma dlinj_eq0 i (x : Obj i) :
  'inj[TLim]_i x = 0 -> exists j (leij : i <= j), bonding leij x = 0.
Proof.
move/dl_eq0 => [j] /dirlimE[k][lejk][leik] Heq.
by exists k; exists leik; rewrite -Heq raddf0.
Qed.

End ZmodDirLimTheory.


#[key="TLim"]
HB.mixin Record isRingDirLim
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
    (TLim : Type) of DirLim disp Sys TLim & Ring TLim := {
  dlinj_is_multiplicative :
    forall i, multiplicative ('inj[TLim]_i)
  }.

#[short(type="ringDirLimType")]
HB.structure Definition RingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of ZmodDirLim disp Sys TLim
    & isRingDirLim disp I Obj bonding Sys TLim
    & Ring TLim
  }.

Section RingDirLimTheory.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> ringType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : ringDirLimType Sys.
Implicit Type x y : TLim.

HB.instance Definition _ i :=
  isMultiplicative.Build (Obj i) TLim _ (dlinj_is_multiplicative i).

Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_multiplicative : multiplicative ('ind[TLim] Hcone).
Proof.
split=> /= [u v|].
- case: (dirlim2P u v) => i x y <-{u} <-{v}.
  by rewrite -rmorphM /= !injindE rmorphM.
- have <- : 'inj[TLim]_(dirsys_inh Sys) 1 = 1 by exact: rmorph1.
  by rewrite injindE rmorph1.
Qed.
HB.instance Definition _ :=
  isMultiplicative.Build TLim T _ dlind_is_multiplicative.

End UniversalProperty.

Lemma dl_eq1 x : x = 1 -> exists i, 'inj[TLim]_i 1 = x.
Proof.
case: (dirlimP x) => i y <-{x} eqinj; exists i.
by rewrite {}eqinj rmorph1.
Qed.

Lemma dlinj_eq1 i (x : Obj i) :
  'inj[TLim]_i x = 1 -> exists j (leij : i <= j), bonding leij x = 1.
Proof.
move/dl_eq1 => [j] /dirlimE[k][lejk][leik] Heq.
by exists k; exists leik; rewrite -Heq rmorph1.
Qed.

End RingDirLimTheory.


#[short(type="comRingDirLimType")]
HB.structure Definition ComRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of ComRing TLim
    & RingDirLim disp Sys TLim
  }.

#[short(type="unitRingDirLimType")]
HB.structure Definition UnitRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of UnitRing TLim
    & RingDirLim disp Sys TLim
  }.


Section DirLimUnitRingTheory.

Variables
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding).
Variable TLim : unitRingDirLimType Sys.

Lemma dlunitP (u : TLim) :
  reflect (exists i (x : Obj i), 'inj x = u /\ x \is a unit) (u \is a unit).
Proof.
apply (iffP idP) => [/unitrP [uinv][] | [i][x [<-{u} xunit]]]; first last.
  exact: (rmorph_unit (RMorphism.clone _ _ 'inj[TLim]_i _) xunit).
case: (dirlim2P u uinv) => i x y <- <-{u}; rewrite -!rmorphM /=.
move=> /dlinj_eq1 [j][leij]; rewrite rmorphM => yx1.
move=> /dlinj_eq1 [k][leik]; rewrite rmorphM => xy1.
case: (directedP j k) => n lejn lekn.
exists n; exists (bonding (le_trans leij lejn) x).
split; first by rewrite dlinjE.
apply/unitrP; exists (bonding (le_trans leij lejn) y).
rewrite -!(bonding_transE Sys leij lejn).
split; first by rewrite -rmorphM {}yx1 rmorph1.
rewrite !(bonding_transE Sys leij lejn).
rewrite !(bondingE bonding _ (le_trans leik lekn)).
rewrite -!(bonding_transE Sys leik lekn).
by rewrite -rmorphM {}xy1 rmorph1.
Qed.

End  DirLimUnitRingTheory.

#[short(type="comUnitRingDirLimType")]
HB.structure Definition ComUnitRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of ComUnitRing TLim
    & RingDirLim disp Sys TLim
  }.


#[key="TLim"]
  HB.mixin Record isLmodDirLim
    (R : ringType)
    (disp : Datatypes.unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : dirsys bonding)
    (TLim : Type) of DirLim disp Sys TLim & Lmodule R TLim := {
  dlinj_is_linear :
    forall i, linear ('inj[TLim]_i)
  }.

#[short(type="lmodDirLimType")]
HB.structure Definition LmodDirLim
    (R : ringType)
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of ZmodDirLim _ Sys TLim
    & isLmodDirLim R disp I Obj bonding Sys TLim
    & Lmodule R TLim
  }.

Section LmodDirLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : lmodDirLimType Sys.

HB.instance Definition _ i :=
  isLinear.Build R (Obj i) TLim _ _ (dlinj_is_linear i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_linear : linear ('ind Hcone : TLim -> T).
Proof.
move=> t u v.
case: (dirlim2P u v) => i x y <-{u} <-{v}.
by rewrite -linearPZ /= !injindE linearPZ.
Qed.
HB.instance Definition _ :=
  isLinear.Build R TLim T _ _ (dlind_is_linear).

End UniversalProperty.
End LmodDirLimTheory.


#[short(type="lalgDirLimType")]
HB.structure Definition LalgebraDirLim
    (R : ringType)
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of Lalgebra R TLim
    & RingDirLim _ Sys TLim
    & LmodDirLim _ Sys TLim
  }.

Section LAlgDirLimTheory.

Variable (R : ringType).
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : lalgDirLimType Sys.

(* Rebuilt the various instances on a lalgtype. *)
HB.instance Definition _ i := Linear.on 'inj[TLim]_i.
(* Check fun i => 'inj[TLim]_i : {lrmorphism Obj i -> TLim}. *)

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

(* Rebuild the various instances on a lalgtype. *)
HB.instance Definition _ i := Linear.on ('ind[TLim] Hcone).
(* Check 'ind[TLim] Hcone : {lrmorphism T -> TLim}. *)

End UniversalProperty.
End LAlgDirLimTheory.

(* No builder ??? *)
#[short(type="algDirLimType")]
HB.structure Definition AlgebraDirLim
    (R : ringType)
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  := {
    TLim of Algebra R TLim
    & RingDirLim _ Sys TLim
    & LmodDirLim _ Sys TLim
  }.


(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

HB.factory Record DirLim_isZmodDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim_isZmodDirLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

Definition dlzero  : TLim := 'inj[TLim]_(dirsys_inh Sys) 0.
Definition dlopp x : TLim :=
  let: existT i a := projT1 (dirlimSP x) in 'inj[TLim] (- a).
Definition dladd x y : TLim :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[TLim] (a + b).

Lemma dlzeroE i : dlzero = 'inj[TLim]_i 0.
Proof.
rewrite /dlzero -dirlimE.
case: (directedP (dirsys_inh Sys) i) => j le_j le_ij.
by exists j; exists le_j; exists le_ij; rewrite !raddf0.
Qed.
Lemma dloppE i (u : Obj i) : dlopp ('inj u) = 'inj (-u).
Proof.
rewrite /dlopp /=; case: dirlimSP => [[j v]] /= /dirlimE [k][lejk][leik].
move/(congr1 (fun u => 'inj[TLim](-u))).
by rewrite -!raddfN !dlinjE.
Qed.
Lemma dladdE i (x y : Obj i) :
  dladd ('inj x) ('inj y) = 'inj (x + y).
Proof.
rewrite /dladd /=; case: dirlimS2P => [[j [u v]]] /= [].
move/dirlimE => [k][le_jk][le_ik] Hux.
move/dirlimE => [l][le_jl][le_il] Hvy.
rewrite -dirlimE; case: (directedP k l) => m le_km le_lm.
exists m; exists (le_trans le_jk le_km); exists (le_trans le_ik le_km).
rewrite !raddfD; congr (_ + _); first by rewrite -!(bonding_transE Sys) Hux.
rewrite (bondingE bonding _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvy (bonding_transE Sys).
exact: (bondingE bonding).
Qed.

Fact dladdA : associative dladd.
Proof.
move=> a b c; case: (dirlim3P a b c) => i x y z <-{a} <-{b} <-{c}.
by rewrite !dladdE addrA.
Qed.
Fact dladdC : commutative dladd.
Proof.
move=> a b; case: (dirlim2P a b) => i x y <-{a} <-{b}.
by rewrite !dladdE addrC.
Qed.
Fact dladd0r : left_id dlzero dladd.
Proof.
move=> a; case: (dirlimP a) => i x <-{a}.
by rewrite (dlzeroE i) dladdE add0r.
Qed.
Fact dladdNr : left_inverse dlzero dlopp dladd.
Proof.
move=> a; case: (dirlimP a) => i x <-{a}.
by rewrite dloppE dladdE addNr -dlzeroE.
Qed.
HB.instance Definition _ :=
    isZmodule.Build TLim dladdA dladdC dladd0r dladdNr.

Fact dlinj_is_additive i : additive 'inj[TLim]_i.
Proof.
by move=> x y; rewrite {2}/opp /= dloppE {2}/add /= dladdE.
Qed.
HB.instance Definition _ :=
  isZmoduleDirLim.Build _ _ _ _ _ TLim dlinj_is_additive.

HB.end.


HB.factory Record DirLim_isRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim_isRingDirLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  DirLim_isZmodDirLim.Build _ _ _ _ Sys TLim.

Definition dlone  : TLim := 'inj[TLim]_(dirsys_inh Sys) 1.
Definition dlmul x y : TLim :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[TLim] (a * b).

Lemma dloneE i : dlone = 'inj[TLim]_i 1.
Proof.
rewrite /dlone -dirlimE.
case: (directedP (dirsys_inh Sys) i) => j le_j le_ij.
by exists j; exists le_j; exists le_ij; rewrite !rmorph1.
Qed.
Lemma dlmulE i (x y : Obj i) :
  dlmul ('inj x) ('inj y) = 'inj (x * y).
Proof.
rewrite /dlmul /=; case: dirlimS2P => [[j [u v]]] /= [].
move/dirlimE => [k][le_jk][le_ik] Hux.
move/dirlimE => [l][le_jl][le_il] Hvy.
rewrite -dirlimE; case: (directedP k l) => m le_km le_lm.
exists m; exists (le_trans le_jk le_km); exists (le_trans le_ik le_km).
rewrite !rmorphM; congr (_ * _); first by rewrite -!(bonding_transE Sys) Hux.
rewrite (bondingE bonding _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvy (bonding_transE Sys).
exact: (bondingE bonding).
Qed.

Fact dlmulA : associative dlmul.
Proof.
move=> a b c; case: (dirlim3P a b c) => i x y z <-{a} <-{b} <-{c}.
by rewrite !dlmulE mulrA.
Qed.
Fact dlmul1r : left_id dlone dlmul.
Proof.
move=> a; case: (dirlimP a) => i x <-{a}.
by rewrite (dloneE i) !dlmulE mul1r.
Qed.
Fact dlmulr1 : right_id dlone dlmul.
Proof.
move=> a; case: (dirlimP a) => i x <-{a}.
by rewrite (dloneE i) !dlmulE mulr1.
Qed.
Fact dlmulDl : left_distributive dlmul +%R.
Proof.
move=> a b c; case: (dirlim3P a b c) => i x y z <-{a} <-{b} <-{c}.
by rewrite !dlmulE -!raddfD /= -mulrDl dlmulE.
Qed.
Fact dlmulDr : right_distributive dlmul +%R.
Proof.
move=> a b c; case: (dirlim3P a b c) => i x y z <-{a} <-{b} <-{c}.
by rewrite !dlmulE -!raddfD /= -mulrDr dlmulE.
Qed.
Fact dlone_neq0 : dlone != 0.
Proof.
apply/negP => /eqP.
rewrite /dlone => /dlinj_eq0 [i] [le_j].
by rewrite [_ 1]rmorph1=> /eqP; rewrite oner_eq0.
Qed.
HB.instance Definition _ :=
  GRing.Zmodule_isRing.Build TLim
    dlmulA dlmul1r dlmulr1 dlmulDl dlmulDr dlone_neq0.

Fact dlinj_is_multiplicative i : multiplicative 'inj[TLim]_i.
Proof.
split => [a b|].
- by rewrite {2}/GRing.mul /= dlmulE.
- by rewrite {2}/GRing.one /= (dloneE i).
Qed.
HB.instance Definition _ :=
  isRingDirLim.Build _ _ _ _ _ TLim dlinj_is_multiplicative.

HB.end.


HB.factory Record DirLim_isComRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> comRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim_isComRingDirLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  DirLim_isRingDirLim.Build _ _ _ _ Sys TLim.

Fact dlmulC x y : x * y = y * x.
Proof.
case: (dirlim2P x y) => i u v <-{x} <-{y}.
by rewrite -!rmorphM mulrC.
Qed.
HB.instance Definition _ :=
  GRing.Ring_hasCommutativeMul.Build TLim dlmulC.

HB.end.


HB.factory Record DirLim_isUnitRingDirLim
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim _ Sys TLim := {}.
HB.builders Context
    (disp : Datatypes.unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : dirsys bonding)
  TLim of DirLim_isUnitRingDirLim _ _ _ _ Sys TLim.

Implicit Type x y : TLim.

HB.instance Definition _ :=
  DirLim_isRingDirLim.Build _ _ _ _ Sys TLim.

Definition dlunit x :=
  `[< exists p : {i & Obj i},
        ('inj[TLim] (projT2 p) == x) && (projT2 p \is a unit) >].
Definition dlinv x : TLim :=
  if (boolP (dlunit x)) is AltTrue pf then
    let: exist p _ := cid (exists_asboolP _ pf) in 'inj[TLim] ((projT2 p)^-1)
    else x.

Fact dlmulVr : {in dlunit, left_inverse 1 dlinv *%R}.
Proof.
move=> a; rewrite /dlinv unfold_in -/(dlunit a).
case (boolP (dlunit a)) => //; rewrite /dlunit => Hunit _ /=.



have /andP [/eqP Heq Hun] := xchoosebP Hunit.
by rewrite -[X in _* X]Heq -rmorphM /= mulVr // rmorph1.

Module DirLimitUnitRing.
Section DirLimitUnitRing.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type x y : TLim.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].

Definition dlunit x :=
  `[exists p : {i & Obj i},
       ('inj[TLim] (projT2 p) == x) && (projT2 p \is a GRing.unit)].
Definition dldir x : TLim :=
  if (boolP (dlunit x)) is AltTrue pf then
    let p := xchooseb pf in 'inj ((projT2 p)^-1) else x.

Program Definition dirlim_unitRingMixin of (phant TLim) :=
  Eval hnf in @UnitRingMixin _ dlunit dldir _ _ _ _.
Next Obligation.
move=> a.
rewrite /dldir unfold_in -/(dlunit a).
case (boolP (dlunit a)) => //; rewrite /dlunit => Hunit _.
have /andP [/eqP Heq Hun] := xchoosebP Hunit.
by rewrite -[X in _* X]Heq -rmorphM /= mulVr // rmorph1.
Qed.
Next Obligation.
move=> a.
rewrite /dldir unfold_in -/(dlunit a).
case (boolP (dlunit a)) => //; rewrite /dlunit => Hunit _.
have /andP [/eqP Heq Hun] := xchoosebP Hunit.
by rewrite -[X in X * _]Heq -rmorphM /= mulrV // rmorph1.
Qed.
Next Obligation.
case: dl1E => [i1 Hi1].
case: (get_repr2 x y) => i [u] [v] [Hx Hy]; subst x y.
move: H0 H1; rewrite -!rmorphM /= -{}Hi1.
rewrite dirlimE => [[il le_i_il le_il Hl]].
rewrite dirlimE => [[ir le_i_ir le_ir Hr]].
move: Hl Hr; rewrite !rmorphM !rmorph1 {le_il le_ir i1}.
case: (directedP il ir) => m le_ilm le_irm.
move/(congr1 (bonding le_ilm)); rewrite !rmorphM rmorph1 => Hl.
move/(congr1 (bonding le_irm)); rewrite !rmorphM rmorph1 => Hr.
move: Hl Hr; rewrite !(bonding_transE Sys).
have -> : bonding (le_trans le_i_il le_ilm) u = bonding (le_trans le_i_ir le_irm) u.
  exact: (bondingE bonding).
have -> : bonding (le_trans le_i_il le_ilm) v = bonding (le_trans le_i_ir le_irm) v.
  exact: (bondingE bonding).
set bu := bonding _ u; set bv := bonding _ v => Hvu Huv.
apply/existsbP; exists (existT _ m bu) => /=; apply/andP; split.
  by rewrite /bu; have /= -> := inj_cocone TLim _ u.
by apply/unitrP; exists bv.
Qed.
Next Obligation.
move=> a; rewrite /dldir; case (boolP (dlunit a)) => // H1 H2; exfalso.
by move: H2; rewrite inE /=; have -> : a \in dlunit by [].
Qed.
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim (dirlim_unitRingMixin (Phant TLim)).

Lemma dlunitP a :
  reflect (exists i (x : Obj i), 'inj[TLim] x = a /\ x \is a GRing.unit)
          (a \is a GRing.unit).
Proof.
rewrite {2}/GRing.unit /= unfold_in /dlunit; apply (iffP (existsbP _)).
- by move=> [[i x]/= /andP[/eqP Heq Hunit]]; exists i; exists x.
- by move=> [i] [x] [<- Hunit]; exists (existT _ i x); rewrite eq_refl.
Qed.

End DirLimitUnitRing.
End DirLimitUnitRing.

Notation "[ 'unitRingMixin' 'of' U 'by' <- ]" :=
  (DirLimitUnitRing.dirlim_unitRingMixin (Phant U))
  (at level 0, format "[ 'unitRingMixin'  'of'  U  'by'  <- ]") : form_scope.

Definition dlunitP := DirLimitUnitRing.dlunitP.


Module DirLimitIDomain.
Section DirLimitIDomain.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (x y : TLim).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical TLim_comRingType :=
  Eval hnf in ComRingType TLim [comRingMixin of TLim by <-].
Local Canonical TLim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].

Fact dlmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> Heq; apply/orP.
case: dl0E => [i0 Hi0].
case: (get_repr2 x y) => i [u] [v] [Hx Hy]; subst x y.
move: Heq; rewrite -!rmorphM /= -{}Hi0.
rewrite dirlimE => [[l le_il le_i0l]].
rewrite !rmorphM !rmorph0 {le_i0l i0} => /eqP.
by rewrite mulf_eq0 => /orP [] /eqP /(congr1 'inj[TLim]) H; [left|right];
   move: H; have /= -> := inj_cocone TLim _ _ => ->; rewrite rmorph0.
Qed.
Definition dirlim_idomainMixin of phant TLim := dlmul_eq0.

End DirLimitIDomain.
End DirLimitIDomain.

Notation "[ 'idomainMixin' 'of' U 'by' <- ]" :=
  (DirLimitIDomain.dirlim_idomainMixin (Phant U))
  (at level 0, format "[ 'idomainMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitLinear.
Section DirLimitLinear.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b c : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].

Definition dlscale r a : TLim := 'inj (r *: projT2 (dlrepr a)).

Lemma dlscaleE r i (x : Obj i) : dlscale r ('inj x) = 'inj (r *: x).
Proof.
rewrite dirlimE.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra.
rewrite dirlimE => [[j le_iaj le_ij Hbond]].
by exists j le_iaj le_ij; rewrite !linearZ Hbond.
Qed.

Program Definition dirlim_lmodMixin of phant TLim :=
  @LmodMixin R [zmodType of TLim] dlscale _ _ _ _.
Next Obligation.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite [dlscale b _]dlscaleE !dlscaleE scalerA.
Qed.
Next Obligation.
move=> v.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite dlscaleE scale1r.
Qed.
Next Obligation.
move=> r a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite !dlscaleE -!raddfD /= dlscaleE.
Qed.
Next Obligation.
move=> r s.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite !dlscaleE -raddfD /= -scalerDl.
Qed.
Local Canonical dirlim_lmodType :=
  Eval hnf in LmodType R TLim (dirlim_lmodMixin (Phant TLim)).

Fact dlinj_is_linear i : linear 'inj_i.
Proof.
move=> r a b.
by rewrite [in RHS]/GRing.scale /= dlscaleE -raddfD.
Qed.
Canonical dlinj_linear i : {linear Obj i -> TLim } :=
  AddLinear (@dlinj_is_linear i).


Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear (Obj i) -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_linear : linear (\ind Hcone).
Proof.
move=> /= r a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearP !injindE -linearP.
Qed.
Canonical dlind_linear : {linear TLim -> T} := AddLinear dlind_is_linear.

End UniversalProperty.

End DirLimitLinear.
End DirLimitLinear.

Notation "[ 'lmodMixin' 'of' U 'by' <- ]" :=
  (DirLimitLinear.dirlim_lmodMixin (Phant U))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_linear := DirLimitLinear.dlinj_linear.
Canonical dlind_linear := DirLimitLinear.dlind_linear.


Module DirLimitLalg.
Section DirLimitLalg.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j }.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b c : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_lmodType :=
  Eval hnf in LmodType R TLim [lmodMixin of TLim by <-].

Fact dlscaleAl r a b : r *: (a * b) = r *: a * b.
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearZ /= -!rmorphM /= -linearZ /= -scalerAl.
Qed.
Definition dirlim_lalgMixin of phant TLim := dlscaleAl.
Local Canonical dirlim_lalgType := Eval hnf in LalgType R TLim dlscaleAl.

Canonical dlinj_lrmorphism i : {lrmorphism Obj i -> TLim} :=
  AddLRMorphism (DirLimitLinear.dlinj_is_linear TLim (i := i)).

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism (Obj i) -> T }).
Hypothesis Hcone : cocone Sys f.
Canonical dlind_lrmorphism : {lrmorphism TLim -> T} :=
  AddLRMorphism (DirLimitLinear.dlind_is_linear Hcone).

End UniversalProperty.

End DirLimitLalg.
End DirLimitLalg.

Notation "[ 'lalgMixin' 'of' U 'by' <- ]" :=
  (DirLimitLalg.dirlim_lalgMixin (Phant U))
  (at level 0, format "[ 'lalgMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_lrmorphism := DirLimitLalg.dlinj_lrmorphism.
Canonical dlind_lrmorphism := DirLimitLalg.dlind_lrmorphism.


Module DirLimitAlg.
Section DirLimitAlg.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variables (R : comRingType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_lmodType :=
  Eval hnf in LmodType R TLim [lmodMixin of TLim by <-].
Local Canonical dirlim_lalgType :=
  Eval hnf in LalgType R TLim [lalgMixin of TLim by <-].

Fact dlscaleAr r a b : r *: (a * b) = a * (r *: b).
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearZ /= -!rmorphM /= -linearZ /= -scalerAr.
Qed.
Definition dirlim_algMixin of phant TLim := dlscaleAr.
Canonical dirlim_algType := Eval hnf in AlgType R TLim dlscaleAr.

End DirLimitAlg.
End DirLimitAlg.

Notation "[ 'algMixin' 'of' U 'by' <- ]" :=
  (DirLimitAlg.dirlim_algMixin (Phant U))
  (at level 0, format "[ 'algMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitField.
Section DirLimitField.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical TLim_comRingType :=
  Eval hnf in ComRingType TLim [comRingMixin of TLim by <-].
Local Canonical dirlim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].
Local Canonical TLim_idomainType :=
  Eval hnf in IdomainType TLim [idomainMixin of TLim by <-].

Fact dirlim_fieldMixin of phant TLim :
  GRing.Field.mixin_of [unitRingType of TLim].
Proof.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia xa <-{a} Hxa.
have : xa != 0 by move: Hxa; apply contra => /eqP ->; rewrite raddf0.
rewrite -unitfE => Ha.
by apply/dlunitP; exists ia; exists xa.
Qed.

End DirLimitField.
End DirLimitField.

Notation "[ 'fieldMixin' 'of' U 'by' <- ]" :=
  (DirLimitField.dirlim_fieldMixin (Phant U))
  (at level 0, format "[ 'fieldMixin'  'of'  U  'by'  <- ]") : form_scope.

Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for direct limits                             *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.

Record dirlim := DirLim {
                     dlpair : {i & Obj i};
                     _ : dlcanon bonding dlpair == dlpair;
                   }.

Definition dirlim_of of phantom (dirsys bonding) Sys := dirlim.
Identity Coercion type_dirlim_of : dirlim_of >-> dirlim.

Local Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).


Canonical dirlim_eqType := EqType dirlim gen_eqMixin.
Canonical dirlimp_eqType := EqType {dirlim Sys} gen_eqMixin.
Canonical dirlim_choiceType := ChoiceType dirlim gen_choiceMixin.
Canonical dirlimp_choiceType := ChoiceType {dirlim Sys} gen_choiceMixin.
Canonical dirlimp_subType := [subType for dlpair].

End Implem.
Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).


Section DirectLimitTheory.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.

Variable Sys : dirsys bonding.
Implicit Type (i j k : I) (a b : {dirlim Sys}).

Definition dlinj_fun i (x : Obj i) := dlcanon bonding (existT _ i x).
Lemma dlinj_spec i (x : Obj i) : dlcanon bonding (dlinj_fun x) == dlinj_fun x.
Proof. by rewrite /dlinj_fun dlcanon_id. Qed.
Definition dlinj i (x : Obj i) : {dirlim Sys} := DirLim (dlinj_spec x).

Lemma dlinjP i (x : Obj i) : dsyscongr bonding x (projT2 (dlpair (dlinj x))).
Proof.
rewrite /dlinj /= /dlinj_fun /=.
exact: (dlcanonP bonding (existT _ i x)).
Qed.

Local Notation "''inj_' i" := (@dlinj i).

(** Budlding the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Obj i -> T).

Definition dlind of cocone Sys f := fun a => f (projT2 (dlpair a)).

Hypothesis Hcone : cocone Sys f.

Lemma dlindP i (x : Obj i) : dlind Hcone ('inj_i x) = f x.
Proof.
rewrite /dlind; apply (dsyscongrE Hcone).
by rewrite dsyscongr_sym; apply: (dlinjP x).
Qed.

Lemma dlindE i j (x : Obj i) (y : Obj j) :
  dsyscongr bonding x y -> dlind Hcone ('inj_i x) = dlind Hcone ('inj_j y).
Proof. by rewrite !dlindP => /(dsyscongrE Hcone). Qed.

End UniversalProperty.

End DirectLimitTheory.


Section InterSpec.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, (i <= j)%O -> Obj i -> Obj j.
Variable Sys : dirsys bonding.

Program Definition dirlim_Mixin :=
  @DirLimMixin disp I Obj bonding Sys {dirlim Sys}
               (dlinj Sys) (dlind (Sys := Sys)) _ _ _.
Next Obligation.
move=> i j le_ij x /=; apply val_inj => /=.
rewrite /dlinj_fun /= -(dlcanonE Sys) /= dsyscongr_sym.
exact: dsyscongr_bonding.
Qed.
Next Obligation. by move=> x /=; rewrite dlindP. Qed.
Next Obligation.
move=> [[i x] /= Hx].
suff -> : (DirLim Hx) = dlinj Sys x by rewrite dlindP -(H i x).
by apply val_inj => /=; rewrite /dlinj_fun (eqP Hx).
Qed.
Canonical dirlim_dirlimType := DirLimType {dirlim Sys} dirlim_Mixin.

End InterSpec.


Open Scope ring_scope.
Section Canonicals.

Variables (disp : Datatypes.unit) (I : dirType disp).

Section ZModule.
Variable Obj : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_zmodType :=
  Eval hnf in ZmodType {dirlim Sys} [zmodMixin of {dirlim Sys} by <-].
End ZModule.

Section Ring.
Variable Obj : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_ringType :=
  Eval hnf in RingType {dirlim Sys} [ringMixin of {dirlim Sys} by <-].
End Ring.

Section ComRing.
Variable Obj : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_comRingType :=
  Eval hnf in ComRingType {dirlim Sys} [comRingMixin of {dirlim Sys} by <-].
End ComRing.

Section UnitRing.
Variable Obj : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_unitRingType :=
  Eval hnf in UnitRingType {dirlim Sys} [unitRingMixin of {dirlim Sys} by <-].
End UnitRing.

Section ComUnitRing.
Variable Obj : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlimp_comUnitRingType := [comUnitRingType of {dirlim Sys}].
End ComUnitRing.

Section IDomain.
Variable Obj : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_idomainType :=
  Eval hnf in IdomainType {dirlim Sys} [idomainMixin of {dirlim Sys} by <-].
End IDomain.

Section Linear.
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_lmodType :=
  Eval hnf in LmodType R {dirlim Sys} [lmodMixin of {dirlim Sys} by <-].
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_lalgType :=
  Eval hnf in LalgType R {dirlim Sys} [lalgMixin of {dirlim Sys} by <-].
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_algType :=
  Eval hnf in AlgType R {dirlim Sys} [algMixin of {dirlim Sys} by <-].
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Obj : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlimp_unitAlgType := [unitAlgType R of {dirlim Sys}].
End UnitAlg.

Section Field.
Variable Obj : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Canonical dirlim_fieldType :=
  Eval hnf in FieldType {dirlim Sys} [fieldMixin of {dirlim Sys} by <-].
End Field.

End Canonicals.


Section Test.
Variable (R : comRingType).
Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : dirsys bonding.
Let test := [algType R of {dirlim Sys}].
End Test.



Section DirLimitChoiceType.

Variables (disp : Datatypes.unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : dirsys bonding.

Implicit Types (i j k : I) (p q : {i & Obj i}).
Local Notation dlc := (dsyscongr bonding).

Lemma dlcanon_ex p : exists q, (fun q => `[< dlc (projT2 p) (projT2 q)>]) q.
Proof. by exists p; apply/asboolP/dsyscongr_refl. Qed.
Definition dlcanon p : {i & Obj i} := xchoose (dlcanon_ex p).

Lemma dlcanonP p : dlc (projT2 p) (projT2 (dlcanon p)).
Proof.
apply/asboolP.
exact: (@xchooseP _ (fun q => `[< dlc (projT2 p) (projT2 q)>])).
Qed.
Lemma dlcanonE p q : dlc (projT2 p) (projT2 q) <-> dlcanon p = dlcanon q.
Proof.
split => [|Heq].
- rewrite /dlcanon => Hcongr; apply: eq_xchoose => /= x.
  apply: asbool_equiv_eq; split; apply: dsyscongr_trans => //.
  exact: dsyscongr_sym_impl.
- rewrite dsyscongr_sym; have /(dsyscongr_trans Sys) := dlcanonP q; apply.
  rewrite dsyscongr_sym -Heq.
  exact: dlcanonP.
Qed.

Lemma dlcanon_id p : dlcanon (dlcanon p) = dlcanon p.
Proof. by apply dlcanonE; rewrite dsyscongr_sym; apply: dlcanonP. Qed.

Variable TLim : dirLimType Sys.
Implicit Types (t a b c : TLim).

Lemma dirlimEI (i : I) (x : Obj i) (y : Obj i) :
  'inj[TLim] x = 'inj[TLim] y ->
  exists (k : I) (le_ik : i <= k), bonding le_ik x = bonding le_ik y.
Proof.
move => Heq; apply contrapT; rewrite -forallNP => Hbond.
have Hcone := cocone_dsyscongr Sys y.
have:= injindE TLim Hcone y; rewrite -Heq injindE.
have /asboolP -> := dsyscongr_refl bonding y.
move=> /asboolP [j le_ij le_ij2] Habs.
apply: (Hbond j); exists (le_ij); rewrite Habs.
exact: bondingE.
Qed.

Lemma dirlimE (i j : I) (x : Obj i) (y : Obj j) :
  ('inj[TLim] x = 'inj[TLim] y) <-> (dsyscongr bonding x y).
Proof.
split => [H | [k le_ik le_jk Hbond]].
- have [l le_il le_jl] := directedP i j.
  have /dirlimEI [k [le_lk]] :
      'inj[TLim] (bonding le_il x) = 'inj[TLim] (bonding le_jl y).
    have /= -> := (inj_cocone TLim le_il x).
    by rewrite H -(inj_cocone TLim le_jl y).
  rewrite !bonding_transE // => Hk.
  exact: (Dsyscongr (le_trans le_il le_lk) (le_trans le_jl le_lk)).
- have /= <- := (inj_cocone TLim le_ik x).
  by rewrite Hbond -(inj_cocone TLim le_jk y).
Qed.

Lemma dlrepc_ex t :
  exists q, (fun q => `[< 'inj (projT2 q) = t >]) q.
Proof. by case: (dirlim_pairP t) => p Hp; exists p; apply/asboolP. Qed.
Definition dlrepr t : {i & Obj i} := xchoose (dlrepc_ex t).

Lemma dlreprP t : 'inj (projT2 (dlrepr t)) = t.
Proof.
apply/asboolP.
exact: (@xchooseP _ (fun q : {i & Obj i} => `[< 'inj (projT2 q) = t >])).
Qed.

Lemma dlrepr_dlcanonE t p : 'inj (projT2 p) = t -> dlcanon p = dlrepr t.
Proof.
move=> <- {t}; apply: eq_xchoose => [[i x]] /=.
by apply: asbool_equiv_eq; rewrite dirlimE dsyscongr_sym.
Qed.


End DirLimitChoiceType.
