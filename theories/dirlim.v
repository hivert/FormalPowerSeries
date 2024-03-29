(** Direct limits *)
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
(** * Direct limits

- {dirlim Sys} == a default implementation of the direct limit of [Sys]
*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order bigop.

Require Import natbar directed.


Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'dirlim' S }" (at level 0, format "{ 'dirlim'  S }").
Reserved Notation "''inj_' i" (at level 8, i at level 2, format "''inj_' i").
Reserved Notation "''inj[' T ']'" (at level 8).
Reserved Notation "''inj[' T ']_' i" (at level 8, i at level 2).
Reserved Notation "''ind[' T ']'" (at level 8).



(***************************************************************************)
(** Direct systems and direct limits                                       *)
(*                                                                         *)
(***************************************************************************)
Section DirectSystem.

Variables (disp : unit) (I : porderType disp).

(** Objects and bonding morphisms of the direct system at left outside     *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Ob : I -> Type.
Variable bonding : (forall i j, i <= j -> Ob i -> Ob j).
Record is_dirsys : Type := IsDirSys {
      dirsys_inh : I;
      dirsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      dirsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hjk) \o (bonding Hij) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition cocone of is_dirsys  :=
  fun T (mors : forall i, Ob i -> T) =>
    forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

Lemma bondingE i j (Hij1 Hij2 : i <= j) : bonding Hij1 =1 bonding Hij2.
Proof. by rewrite (Prop_irrelevance Hij1 Hij2). Qed.

Lemma bonding_transE (Sys : is_dirsys) i j k (Hij : i <= j) (Hjk : j <= k) u :
  (bonding Hjk) (bonding Hij u) = bonding (le_trans Hij Hjk) u.
Proof. by move/dirsys_comp : Sys; apply. Qed.

Lemma coconeE Sys T (mors : forall i, Ob i -> T) :
  cocone Sys mors ->
    forall i j (Hij : i <= j) u, mors j (bonding Hij u) = mors i u.
Proof. by rewrite /cocone => H i j le_ij u; rewrite -(H i j le_ij). Qed.

End DirectSystem.



(***************************************************************************)
(** Interface for direct limits                                            *)
(*                                                                         *)
(***************************************************************************)
Open Scope ring_scope.


#[key="dlT"]
HB.mixin Record isDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  dlT of Choice dlT := {
    dirlim_inj : forall i, Obj i -> dlT;
    dirlim_ind : forall (T : Type) (f : forall i, Obj i -> T),
      (cocone Sys f) -> dlT -> T;
    dlinjP : cocone Sys dirlim_inj;
    dlind_commute : forall T (f : forall i, Obj i -> T) (Hcone : cocone Sys f),
      forall i, dirlim_ind T f Hcone \o dirlim_inj i =1 f i;
    dlind_uniq : forall T (f : forall i, Obj i -> T) (Hcone : cocone Sys f),
      forall (ind : dlT -> T),
        (forall i, ind \o dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind T f Hcone
  }.

#[short(type="dirLimType")]
HB.structure Definition DirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> Type)
    (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  := {
    dlT of isDirLim disp I Obj bonding Sys dlT
    & Choice dlT
  }.



Section InternalTheory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.

Local Notation "''inj'" := (dirlim_inj (s := dlT)).
Local Notation "''inj_' i" := (dirlim_inj (s := dlT) i).
Local Notation "''ind'" := (dirlim_ind (s := dlT) _ _).

Lemma dlinjE :
  forall i j, forall (Hij : i <= j) u, 'inj_j (bonding Hij u) = 'inj_i u.
Proof. by move=> i j Hij u; rewrite [LHS]dlinjP. Qed.

Lemma injindE  T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) i u :
  'ind Hcone ('inj_ i u) = f i u.
Proof. exact: dlind_commute. Qed.

End InternalTheory.

Arguments dlinjP {disp I Obj bonding} [Sys].

Notation "''inj[' dlT ']_' i" := (dirlim_inj (s := dlT) i) (only parsing).
Notation "''inj[' dlT ']'" := ('inj[dlT]_ _)  (only parsing).
Notation "''inj_' i" := ('inj[ _ ]_ i).
Notation "''inj'" := ('inj[ _ ]_ _).
Notation "''ind[' T ']'" := (dirlim_ind (s := T) _ _)  (only parsing).
Notation "''ind'" := ('ind[ _ ]).


Section Theory.

Variables (disp : unit) (I : porderType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Inductive dirlim_spec x : Prop :=
  | DirLimSpec : forall k (u : Obj k), 'inj u = x -> dirlim_spec x.

Lemma dirlimP x : dirlim_spec x.
Proof.
suff: exists k (u : Obj k), 'inj u = x by case=> i [u <-{x}]; exists i u.
rewrite not_existsP => H.
pose f i := pred0 (T := Obj i).
have Hcone : cocone Sys f by [].
have /(dlind_uniq _ _ Hcone)/(_ x) :
  forall i, (pred0 (T := dlT)) \o 'inj =1 f i by [].
suff /(dlind_uniq _ _ Hcone)/(_ x) <- : forall i, (pred1 x) \o 'inj =1 f i.
  by rewrite /= eqxx.
rewrite /f => i u /=; apply/negP => /eqP eq_inj.
by apply/(H i); exists u.
Qed.

Lemma dirlimSP x : { p : {i & Obj i} | 'inj (projT2 p) = x }.
Proof.
by apply cid; have [i u eqinj] := dirlimP x; exists (existT Obj i u).
Qed.

End Theory.


Section DirLimDirected.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.
Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Inductive dirlim2_spec x y : Prop :=
  | DirLim2Spec :
    forall k (u v : Obj k), 'inj u = x -> 'inj v = y
                            -> dirlim2_spec x y.
Inductive dirlim3_spec x y z : Prop :=
  | DirLim3Spec :
    forall k (u v w : Obj k), 'inj u = x -> 'inj v = y -> 'inj w = z
                              -> dirlim3_spec x y z.

Lemma dirlim2P x y : dirlim2_spec x y.
Proof.
have [iu u <-{x}] := dirlimP x.
have [iv v <-{y}] := dirlimP y.
have [n le_ian le_ibn] := directedP iu iv.
by exists n (bonding le_ian u) (bonding le_ibn v); rewrite dlinjE.
Qed.
Lemma dirlimS2P x y :
  { p : {i & (Obj i * Obj i)%type} |
    'inj (projT2 p).1 = x /\ 'inj (projT2 p).2 = y }.
Proof.
apply cid; have [i u v equ eqv] := dirlim2P x y.
by exists (existT _ i (u, v)).
Qed.

Lemma dirlim3P x y z : dirlim3_spec x y z.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
have [j w <-{z}] := dirlimP z.
have [n le_in le_jn] := directedP i j.
by exists n (bonding le_in u) (bonding le_in v) (bonding le_jn w);
  rewrite dlinjE.
Qed.

End DirLimDirected.


Section DirSysCongr.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Implicit Types (i j k : I) (u v : {i : I & Obj i}).
Definition DPair i (u : Obj i) := (existT Obj i u).

Inductive dsysequal (Sys : is_dirsys bonding) u v : Prop :=
  | Dsysequal : forall k (le_ik : projT1 u <= k) (le_jk : projT1 v <= k),
    (bonding le_ik (projT2 u) = bonding le_jk (projT2 v)) -> dsysequal Sys u v.

Definition dsyseq (Sys : is_dirsys bonding) u v := `[< dsysequal Sys u v >].

Lemma dsyseqP u v : reflect (dsysequal Sys u v) (dsyseq Sys u v).
Proof. exact: asboolP. Qed.

Local Arguments Dsysequal {Sys u v k} (le_ik le_jk).

Lemma dsyseq_bonding i j (le_ij : i <= j) (u : Obj i) :
  dsyseq Sys (DPair u) (DPair (bonding le_ij u)).
Proof.
apply/dsyseqP; apply: (Dsysequal (k := j)) => /=.
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dsyseq_refl u : dsyseq Sys u u.
Proof. by apply/dsyseqP; apply: (Dsysequal (k := projT1 u)). Qed.
Lemma dsyseq_sym_impl u v : dsyseq Sys u v -> dsyseq Sys v u.
Proof.
move/dsyseqP => [k le_ik le_jk Hbond].
by apply/dsyseqP; apply: (Dsysequal le_jk le_ik); rewrite Hbond.
Qed.
Lemma dsyseq_sym u v : dsyseq Sys u v = dsyseq Sys v u.
Proof. by apply/idP/idP; apply: dsyseq_sym_impl. Qed.
Lemma dsyseq_trans : transitive (dsyseq Sys).
Proof.
move=> v u w.
move/dsyseqP => [l le_il le_jl Huv].
move/dsyseqP => [m le_jm le_km Hvw].
have [n le_ln le_mn] := directedP l m.
apply/dsyseqP; apply: (Dsysequal (le_trans le_il le_ln) (le_trans le_km le_mn)).
rewrite -!bonding_transE // {}Huv -{}Hvw !bonding_transE //.
exact: bondingE.
Qed.

Canonical SysEq :=
  EquivRel (@dsyseq Sys) dsyseq_refl dsyseq_sym dsyseq_trans.

Lemma cocone_dsyseq u :
  cocone Sys (fun j (v : Obj j) => dsyseq Sys u (DPair v)).
Proof.
move=> j k le_jk v /=.
case: (boolP (dsyseq Sys u (DPair v))) => [/dsyseqP | /dsyseqP Hnthr].
- move=> [l /= le_il le_jl Hbond]; apply/asboolP.
  have [m le_km le_lm] := directedP k l.
  apply: (Dsysequal (le_trans le_il le_lm)) => /=.
  rewrite -(dirsys_comp Sys le_il le_lm) /= Hbond.
  by rewrite !bonding_transE //; apply: bondingE.
- apply/negP => /= /asboolP [l /= le_il le_kl].
  rewrite bonding_transE // => Hbond; apply: Hnthr.
  apply: (Dsysequal le_il) => /=; first exact: le_trans le_jk le_kl.
  by move => le_jl; rewrite Hbond; apply: bondingE.
Qed.


Section Compatibility.

Variables (T : Type) (f : forall i, Obj i -> T).
Hypothesis Hcone : cocone Sys f.

Lemma dsyseqE i j (u : Obj i) (v : Obj j) :
  dsyseq Sys (DPair u) (DPair v) -> f u = f v.
Proof.
move/dsyseqP => [k le_ik le_jk Hbond].
by rewrite -(coconeE Hcone le_ik) Hbond (coconeE Hcone).
Qed.

End Compatibility.

Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Lemma dirlimE i j (u : Obj i) (v : Obj j) :
  ('inj[dlT] u = 'inj[dlT] v) <-> (dsysequal Sys (DPair u) (DPair v)).
Proof.
split => [eqinj | [k leik lejk /(congr1 'inj[dlT])]]; last by rewrite !dlinjE.
suff : exists k (ik : i <= k) (jk : j <= k), bonding ik u = bonding jk v.
  by move=> [k] [ik] [jk] Heq; exists k ik jk.
apply contrapT; rewrite -forallNP => Hbond.
have Hcone := cocone_dsyseq (DPair v).
have:= injindE dlT Hcone v; rewrite -eqinj injindE (dsyseq_refl (DPair v)).
move=> /asboolP [k le_jk le_ik Habs].
apply: (Hbond k); exists (le_ik); exists (le_jk); rewrite Habs.
exact: bondingE.
Qed.

Lemma dirlimeqP i j (u : Obj i) (v : Obj j) :
  reflect ('inj[dlT] u = 'inj[dlT] v) (dsyseq Sys (DPair u) (DPair v)).
Proof. by apply (iffP (dsyseqP _ _)) => /dirlimE. Qed.

Lemma dirlim_is_inj :
  (forall i, injective 'inj[dlT]_i)
  <->
  (forall i j (le_ij : i <= j), injective (bonding le_ij)).
Proof.
split => Hinj.
- move=> i j le_ij u v /(congr1 'inj[dlT]).
  by rewrite !dlinjE; apply: Hinj.
- move=> i u v /dirlimE [k /= le_ik le_ik1].
  by rewrite bondingE /=; apply Hinj.
Qed.

End DirSysCongr.
Arguments Dsysequal {disp I Obj bonding Sys u v k} (le_ik le_jk).
Arguments dsysequal {disp I Obj bonding} (Sys) (u v).
Arguments dsyseq {disp I Obj bonding} (Sys) (u v).


(****************************************************************************)
(**  Interface for inverse limits in various algebraic categories           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)


#[key="ilT"]
HB.mixin Record isNmoduleDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (ilT : Type) of DirLim disp Sys ilT & GRing.Nmodule ilT := {
  dlinj_is_semi_additive :
    forall i, semi_additive ('inj[ilT]_i)
  }.
#[short(type="nmodDirLimType")]
HB.structure Definition NmodDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of DirLim disp Sys dlT
    & isNmoduleDirLim disp I Obj bonding Sys dlT
    & GRing.Nmodule dlT
  }.

Section NmodDirLimTheory.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> nmodType.
Variable bonding : forall i j, i <= j -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : nmodDirLimType Sys.
Implicit Type x y : dlT.

HB.instance Definition _ i :=
  GRing.isSemiAdditive.Build (Obj i) dlT _ (dlinj_is_semi_additive i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : nmodType) (f : forall i, {additive Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_semi_additive : semi_additive ('ind[dlT] Hcone).
Proof.
split => [| /= x y].
  have <- : 'inj[dlT]_(dirsys_inh Sys) 0 = 0 by rewrite raddf0.
  by rewrite injindE raddf0.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -raddfD /= !injindE raddfD.
Qed.
HB.instance Definition _ :=
  GRing.isSemiAdditive.Build dlT T _ dlind_is_semi_additive.

End UniversalProperty.

Lemma dl0E i : 'inj[dlT]_i 0 = 0.
Proof. by rewrite !raddf0. Qed.

Lemma dlinj_eq0 i (u : Obj i) :
  'inj[dlT]_i u = 0 -> exists j (leij : i <= j), bonding leij u = 0.
Proof.
rewrite -(dl0E i) => /dirlimE [k lejk leik Heq].
by exists k; exists lejk; rewrite Heq raddf0.
Qed.

End NmodDirLimTheory.


#[short(type="zmodDirLimType")]
HB.structure Definition ZmodDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmodDirLim disp Sys dlT
    & GRing.Zmodule dlT
  }.


#[key="dlT"]
HB.mixin Record isSemiRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (dlT : Type) of DirLim disp Sys dlT & GRing.SemiRing dlT := {
  dlinj_is_multiplicative :
    forall i, multiplicative ('inj[dlT]_i)
  }.
#[short(type="semiRingDirLimType")]
HB.structure Definition SemiRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of NmodDirLim disp Sys dlT
    & isSemiRingDirLim disp I Obj bonding Sys dlT
    & GRing.SemiRing dlT
  }.

Section SemiRingDirLimTheory.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> semiRingType.
Variable bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : semiRingDirLimType Sys.
Implicit Type x y : dlT.

HB.instance Definition _ i :=
  GRing.isMultiplicative.Build (Obj i) dlT _ (dlinj_is_multiplicative i).

Section UniversalProperty.

Variable (T : semiRingType) (f : forall i, {rmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_multiplicative : multiplicative ('ind[dlT] Hcone).
Proof.
split=> /= [x y|].
- have [i u v <-{x} <-{y}] := dirlim2P x y.
  by rewrite -rmorphM /= !injindE rmorphM.
- have <- : 'inj[dlT]_(dirsys_inh Sys) 1 = 1 by exact: rmorph1.
  by rewrite injindE rmorph1.
Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build dlT T _ dlind_is_multiplicative.

End UniversalProperty.

Lemma dl1E i : 'inj[dlT]_i 1 = 1.
Proof. by rewrite !rmorph1. Qed.

Lemma dlinj_eq1 i (u : Obj i) :
  'inj[dlT]_i u = 1 -> exists j (leij : i <= j), bonding leij u = 1.
Proof.
rewrite -(dl1E i) => /dirlimE [k lejk leik Heq].
by exists k; exists lejk; rewrite Heq rmorph1.
Qed.

End SemiRingDirLimTheory.


#[short(type="ringDirLimType")]
HB.structure Definition RingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of SemiRingDirLim disp Sys dlT
    & GRing.Ring dlT
  }.


#[short(type="comRingDirLimType")]
HB.structure Definition ComSemiRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of SemiRingDirLim disp Sys dlT
    & GRing.ComSemiRing dlT
  }.


#[short(type="comRingDirLimType")]
HB.structure Definition ComRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of SemiRingDirLim disp Sys dlT
    & GRing.ComRing dlT
  }.


#[short(type="unitRingDirLimType")]
HB.structure Definition UnitRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    ilT of SemiRingDirLim disp Sys ilT
    & GRing.UnitRing ilT
  }.

Section DirLimUnitRingTheory.

Variables
    (disp : unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding).
Variable dlT : unitRingDirLimType Sys.
Implicit Type (x y z : dlT).
Lemma dlunitP (x : dlT) :
  reflect
    (exists i (u : Obj i), 'inj[dlT] u = x /\ u \is a GRing.unit)
    (x \is a GRing.unit).
Proof.
apply (iffP idP) => [/unitrP [xinv][] | [i][u [<-{x} uunit]]]; first last.
  exact: (rmorph_unit _ uunit).
have [i u v <-{xinv} <-{x}] := dirlim2P x xinv; rewrite -!rmorphM /=.
move=> /dlinj_eq1 [j][leij]; rewrite rmorphM => vu1.
move=> /dlinj_eq1 [k][leik]; rewrite rmorphM => uv1.
have [n lejn lekn] := directedP j k.
exists n; exists (bonding (le_trans leij lejn) u).
split; first by rewrite dlinjE.
apply/unitrP; exists (bonding (le_trans leij lejn) v).
rewrite -!(bonding_transE Sys leij lejn).
split; first by rewrite -rmorphM {}vu1 rmorph1.
rewrite !(bonding_transE Sys leij lejn).
rewrite !(bondingE bonding _ (le_trans leik lekn)).
rewrite -!(bonding_transE Sys leik lekn).
by rewrite -rmorphM {}uv1 rmorph1.
Qed.

End  DirLimUnitRingTheory.


#[short(type="comUnitRingDirLimType")]
HB.structure Definition ComUnitRingDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    ilT of SemiRingDirLim disp Sys ilT
    & GRing.ComUnitRing ilT
  }.


#[short(type="idomainDirLimType")]
HB.structure Definition IDomainDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of SemiRingDirLim disp Sys dlT
    & GRing.IntegralDomain dlT
  }.


#[short(type="fieldDirLimType")]
HB.structure Definition FieldDirLim
    (disp : unit) (I : porderType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of SemiRingDirLim disp Sys dlT
    & GRing.Field dlT
  }.


#[key="dlT"]
HB.mixin Record isLmodDirLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
    (dlT : Type) of DirLim disp Sys dlT & GRing.Lmodule R dlT := {
  dlinj_is_linear :
    forall i, linear ('inj[dlT]_i)
  }.
#[short(type="lmodDirLimType")]
HB.structure Definition LmodDirLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of ZmodDirLim _ Sys dlT
    & isLmodDirLim R disp I Obj bonding Sys dlT
    & GRing.Lmodule R dlT
  }.

Section LmodDirLimTheory.

Variable (R : ringType).
Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, i <= j -> {linear Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.

Variable dlT : lmodDirLimType Sys.

HB.instance Definition _ i :=
  GRing.isLinear.Build R (Obj i) dlT _ _ (dlinj_is_linear i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_linear : linear ('ind Hcone : dlT -> T).
Proof.
move=> t x y.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -linearPZ /= !injindE linearPZ.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R dlT T _ _ (dlind_is_linear).

End UniversalProperty.
End LmodDirLimTheory.


#[short(type="lalgDirLimType")]
HB.structure Definition LalgebraDirLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of LmodDirLim _ Sys dlT
    & SemiRingDirLim _ Sys dlT
    & GRing.Lalgebra R dlT
  }.

Section LAlgDirLimTheory.

Variable (R : ringType).
Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Variable dlT : lalgDirLimType Sys.

(* Rebuilt the various instances on a lalgtype. *)
HB.instance Definition _ i := GRing.Linear.on 'inj[dlT]_i.
(* Check fun i => 'inj[dlT]_i : {lrmorphism Obj i -> dlT}. *)

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism Obj i -> T}).
Hypothesis Hcone : cocone Sys f.

(* Rebuild the various instances on a lalgtype. *)
HB.instance Definition _ i := GRing.Linear.on ('ind[dlT] Hcone).
(* Check 'ind[dlT] Hcone : {lrmorphism T -> dlT}. *)

End UniversalProperty.
End LAlgDirLimTheory.


#[short(type="algDirLimType")]
HB.structure Definition AlgebraDirLim
    (R : ringType)
    (disp : unit) (I : porderType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  := {
    dlT of LalgebraDirLim _ Sys dlT
    & GRing.Algebra R dlT
  }.

(* What about comAlgType, unitAlgType, comUnitAlgType... ??? *)
(* Not needed unless particular theory need interface    ??? *)


(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)


HB.factory Record DirLim_isNmodDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> nmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isNmodDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

Definition dlzero  : dlT := 'inj[dlT]_(dirsys_inh Sys) 0.
Definition dladd x y : dlT :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[dlT] (a + b).

Local Lemma dlzeroE i : dlzero = 'inj[dlT]_i 0.
Proof.
rewrite /dlzero dirlimE.
have [j le_j le_ij] := directedP (dirsys_inh Sys) i.
by exists j le_j le_ij; rewrite !raddf0.
Qed.
Lemma dladdE i (u v : Obj i) :
  dladd ('inj u) ('inj v) = 'inj (u + v).
Proof.
rewrite /dladd /=; case: dirlimS2P => [[j [x y]]] /= [].
move/dirlimE => [k /= le_jk le_ik Hux].
move/dirlimE => [l /= le_jl le_il Hvy].
rewrite dirlimE; have [m le_km le_lm] := directedP k l.
exists m (le_trans le_jk le_km) (le_trans le_ik le_km).
rewrite !raddfD; congr (_ + _); first by rewrite -!(bonding_transE Sys) Hux.
rewrite (bondingE bonding _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvy (bonding_transE Sys).
exact: (bondingE bonding).
Qed.

Fact dladdA : associative dladd.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dladdE addrA.
Qed.
Fact dladdC : commutative dladd.
Proof.
move=> x y; have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite !dladdE addrC.
Qed.
Fact dladd0r : left_id dlzero dladd.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite (dlzeroE i) dladdE add0r.
Qed.
HB.instance Definition _ :=
    GRing.isNmodule.Build dlT dladdA dladdC dladd0r.

Fact dlinj_is_semi_additive i : semi_additive 'inj[dlT]_i.
Proof.
split; first by rewrite -dlzeroE.
by move=> u v; rewrite {2}/GRing.add /= dladdE.
Qed.
HB.instance Definition _ :=
  isNmoduleDirLim.Build _ _ _ _ _ dlT dlinj_is_semi_additive.

HB.end.


HB.factory Record DirLim_isZmodDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> zmodType)
    (bonding : forall i j, i <= j -> {additive Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isZmodDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isNmodDirLim.Build _ _ _ _ Sys dlT.

Definition dlopp x : dlT :=
  let: existT i a := projT1 (dirlimSP x) in 'inj[dlT] (- a).
Lemma dloppE i (u : Obj i) : dlopp ('inj u) = 'inj (-u).
Proof.
rewrite /dlopp /=; case: dirlimSP => [[j v]] /= /dirlimE [k lejk leik].
move/(congr1 (fun u => 'inj[dlT](-u))).
by rewrite -!raddfN !dlinjE.
Qed.
Fact dladdNr : left_inverse 0 dlopp +%R.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite dloppE -raddfD /= addNr raddf0.
Qed.
HB.instance Definition _ :=
    GRing.Nmodule_isZmodule.Build dlT dladdNr.

Fact dlinj_is_additive i : additive 'inj[dlT]_i.
Proof.
by move=> u v; rewrite {2}/GRing.opp /= dloppE raddfD /=.
Qed.

HB.end.


HB.factory Record DirLim_isSemiRingDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> semiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isSemiRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isNmodDirLim.Build _ _ _ _ Sys dlT.

Definition dlone : dlT := 'inj[dlT]_(dirsys_inh Sys) 1.
Definition dlmul x y : dlT :=
  let: existT i (a, b) := projT1 (dirlimS2P x y) in 'inj[dlT] (a * b).

Lemma dloneE i : dlone = 'inj[dlT]_i 1.
Proof.
rewrite /dlone dirlimE.
have [j le_j le_ij] := directedP (dirsys_inh Sys) i.
by exists j le_j le_ij; rewrite !rmorph1.
Qed.
Lemma dlmulE i (u v : Obj i) :
  dlmul ('inj u) ('inj v) = 'inj (u * v).
Proof.
rewrite /dlmul /=; case: dirlimS2P => [[j [a b]]] /= [].
move/dirlimE => [k /= le_jk le_ik Hua].
move/dirlimE => [l /= le_jl le_il Hvb].
rewrite dirlimE; have [m le_km le_lm] := directedP k l.
exists m (le_trans le_jk le_km) (le_trans le_ik le_km).
rewrite !rmorphM; congr (_ * _); first by rewrite -!(bonding_transE Sys) Hua.
rewrite (bondingE bonding _ (le_trans le_jl le_lm)).
rewrite -(bonding_transE Sys) Hvb (bonding_transE Sys).
exact: (bondingE bonding).
Qed.

Fact dlmulA : associative dlmul.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE mulrA.
Qed.
Fact dlmul1r : left_id dlone dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite (dloneE i) !dlmulE mul1r.
Qed.
Fact dlmulr1 : right_id dlone dlmul.
Proof.
move=> a; have [i x <-{a}] := dirlimP a.
by rewrite (dloneE i) !dlmulE mulr1.
Qed.
Fact dlmulDl : left_distributive dlmul +%R.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE -!raddfD /= -mulrDl dlmulE.
Qed.
Fact dlmulDr : right_distributive dlmul +%R.
Proof.
move=> x y z; have [i u v w <-{x} <-{y} <-{z}] := dirlim3P x y z.
by rewrite !dlmulE -!raddfD /= -mulrDr dlmulE.
Qed.
Fact dlmul0r : left_zero 0 dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite -(raddf0 'inj[dlT]_i) dlmulE mul0r.
Qed.
Fact dlmulr0 : right_zero 0 dlmul.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite -(raddf0 'inj[dlT]_i) dlmulE mulr0.
Qed.
Fact dlone_neq0 : dlone != 0.
Proof.
apply/negP => /eqP.
rewrite /dlone => /dlinj_eq0 [i] [le_j].
by rewrite [_ 1]rmorph1=> /eqP; rewrite oner_eq0.
Qed.
HB.instance Definition _ :=
  GRing.Nmodule_isSemiRing.Build dlT
    dlmulA dlmul1r dlmulr1 dlmulDl dlmulDr dlmul0r dlmulr0 dlone_neq0.

Fact dlinj_is_multiplicative i : multiplicative 'inj[dlT]_i.
Proof.
split => [u v|].
- by rewrite {2}/GRing.mul /= dlmulE.
- by rewrite {2}/GRing.one /= (dloneE i).
Qed.
HB.instance Definition _ :=
  isSemiRingDirLim.Build _ _ _ _ _ dlT dlinj_is_multiplicative.

HB.end.


HB.factory Record DirLim_isRingDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> ringType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isZmodDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isSemiRingDirLim.Build _ _ _ _ Sys dlT.

HB.end.


HB.factory Record DirLim_isComSemiRingDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> comSemiRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComSemiRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isSemiRingDirLim.Build _ _ _ _ Sys dlT.

Fact dlmulC x y : x * y = y * x.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -!rmorphM mulrC.
Qed.
HB.instance Definition _ :=
  GRing.SemiRing_hasCommutativeMul.Build dlT dlmulC.

HB.end.


(** ComRingInvLim is just a join *)


HB.factory Record DirLim_isUnitRingDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isUnitRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isRingDirLim.Build _ _ _ _ Sys dlT.

Definition dlunit x :=
  `[< exists p : {i & Obj i},
        ('inj[dlT] (projT2 p) == x) && (projT2 p \is a GRing.unit) >].

Fact dir_isunitP x :
  dlunit x ->
  {p : {i & Obj i} | 'inj[dlT] (projT2 p) = x /\ projT2 p \is a GRing.unit}.
Proof.
by rewrite /dlunit => /asboolP/cid [p] /andP[/eqP Heq Hunit]; exists p.
Qed.

Definition dlinv x : dlT :=
  if (boolP (dlunit x)) is AltTrue pf then
    let: exist p _ := dir_isunitP pf in 'inj[dlT] ((projT2 p)^-1)
    else x.

Fact dlmulVr : {in dlunit, left_inverse 1 dlinv *%R}.
Proof.
move=> x; rewrite /dlinv unfold_in -/(dlunit x).
case (boolP (dlunit x)) => //; rewrite /dlunit => Hunit _ /=.
case: (dir_isunitP Hunit) => [][ix inv /= [eqinv unitinv]].
by rewrite -eqinv -rmorphM /= mulVr // rmorph1.
Qed.
Fact dlmulrV : {in dlunit, right_inverse 1 dlinv *%R}.
Proof.
move=> x; rewrite /dlinv unfold_in -/(dlunit x).
case (boolP (dlunit x)) => //; rewrite /dlunit => Hunit _ /=.
case: (dir_isunitP Hunit) => [][ix inv /= [eqinv unitinv]].
by rewrite -eqinv -rmorphM /= mulrV // rmorph1.
Qed.
Fact dlunit_impl x y : y * x = 1 /\ x * y = 1 -> dlunit x.
Proof.
have [i u v <-{x} <-{y} []] := dirlim2P x y.
rewrite -!rmorphM /= -(dl1E dlT i).
move/dirlimE => [j le_ij le_j Hl].
move/dirlimE => [k le_ik le_k Hr].
move: Hl Hr; rewrite !rmorphM !rmorph1 {le_j le_k}.
have [l le_jl le_kl] := directedP j k.
move/(congr1 (bonding _ _ le_jl)); rewrite !rmorphM rmorph1 => Hl.
move/(congr1 (bonding _ _ le_kl)); rewrite !rmorphM rmorph1 => Hr.
move: Hl Hr; rewrite !(bonding_transE Sys).
rewrite !(bondingE bonding _ (le_trans le_ij le_jl)).
set bu := bonding _ _ _ u; set bv := bonding _ _ _ v => Hvu Huv.
apply/asboolP.
exists (DPair bu) => /=; apply/andP; split; first by rewrite /bu dlinjE.
by apply/unitrP; exists bv.
Qed.
Fact dlinv0id : {in [predC dlunit], dlinv =1 id}.
Proof.
move=> a; rewrite /dlinv; case (boolP (dlunit a)) => // H1 H2; exfalso.
by move: H2; rewrite !unfold_in /=; have -> : a \in dlunit by [].
Qed.

HB.instance Definition _ :=
  GRing.Ring_hasMulInverse.Build dlT dlmulVr dlmulrV dlunit_impl dlinv0id.

HB.end.


(** ComUnitRingInvLim is just a join *)


HB.factory Record DirLim_isIDomainDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isIDomainDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isUnitRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isComSemiRingDirLim.Build _ _ _ _ Sys dlT.

Fact dlmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> Heq; apply/orP; move: Heq.
have [i u v <-{x} <-{y}] := dirlim2P x y.
rewrite -!rmorphM /= => /dlinj_eq0 [j] [le_ij] /=.
rewrite rmorphM => /eqP.
by rewrite mulf_eq0 => /orP [] /eqP /(congr1 'inj[dlT]) H; [left|right];
   move: H; have /= -> := dlinjE dlT _ _ => ->; rewrite rmorph0.
Qed.
HB.instance Definition _ :=
  GRing.ComUnitRing_isIntegral.Build dlT dlmul_eq0.

HB.end.


HB.factory Record DirLim_isFieldDirLim
    (disp : unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (disp : unit) (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isFieldDirLim _ _ _ _ Sys dlT.

HB.instance Definition _ :=
  DirLim_isIDomainDirLim.Build _ _ _ _ Sys dlT.

Fact dirlim_field_axiom : GRing.field_axiom dlT.
Proof.
move=> x; have [i u <-{x} Hu] := dirlimP x.
have : u != 0 by move: Hu; apply contra => /eqP ->; rewrite raddf0.
rewrite -unitfE => uunit.
by apply/dlunitP; exists i; exists u.
Qed.
HB.instance Definition _ :=
    GRing.UnitRing_isField.Build dlT dirlim_field_axiom.

HB.end.


HB.factory Record DirLim_isLmoduleDirLim
    (R : ringType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : ringType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> lmodType R)
    (bonding : forall i j, i <= j -> {linear Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isLmoduleDirLim R _ _ _ _ Sys dlT.

Implicit Type (x y : dlT) (r : R).

HB.instance Definition _ :=
  DirLim_isZmodDirLim.Build _ _ _ _ Sys dlT.

Definition dlscale r x : dlT :=
  let: existT i u := projT1 (dirlimSP x) in 'inj (r *: u).

Lemma dlscaleE r i (u : Obj i) : dlscale r ('inj u) = 'inj (r *: u).
Proof.
rewrite /dlscale; case: dirlimSP => [[j v /=]].
rewrite !dirlimE => [][k /= le_ik le_jk eq_uv].
by exists k le_ik le_jk; rewrite !linearZ /= eq_uv.
Qed.

Fact dlscaleA a b x : dlscale a (dlscale b x) = dlscale (a * b) x.
Proof.
have [i u <-{x}] := dirlimP x.
by rewrite [dlscale b _]dlscaleE !dlscaleE scalerA.
Qed.
Fact dlscale1 : left_id 1 dlscale.
Proof.
move=> x; have [i u <-{x}] := dirlimP x.
by rewrite dlscaleE scale1r.
Qed.
Fact dlscaleDr : right_distributive dlscale +%R.
Proof.
move=> r x y; have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite !dlscaleE -!raddfD /= dlscaleE.
Qed.
Fact dlscaleDl x : {morph dlscale^~ x: a b / a + b}.
Proof.
move=> a b; have [i u <-{x}] := dirlimP x.
by rewrite !dlscaleE -raddfD /= -scalerDl.
Qed.
HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R dlT dlscaleA dlscale1 dlscaleDr dlscaleDl.

Fact dlinj_is_linear i : linear 'inj[dlT]_i.
Proof.
move=> r x y.
by rewrite [in RHS]/GRing.scale /= dlscaleE -raddfD.
Qed.
HB.instance Definition _ :=
  isLmodDirLim.Build R _ _ _ _ _ dlT dlinj_is_linear.

HB.end.


HB.factory Record DirLim_isLalgDirLim
    (R : ringType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : ringType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> lalgType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isLalgDirLim R _ _ _ _ Sys dlT.

Implicit Type (x y : dlT) (r : R).

HB.instance Definition _ :=
  DirLim_isRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  DirLim_isLmoduleDirLim.Build R _ _ _ _ Sys dlT.

Fact dlscaleAl r x y : r *: (x * y) = r *: x * y.
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -[r *: _ u]linearZ /= -!rmorphM /= -linearZ /= -scalerAl.
Qed.
HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R dlT dlscaleAl.

HB.end.


HB.factory Record DirLim_isAlgebraDirLim
    (R : comRingType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    (R : comRingType)
    (disp : unit) (I : dirType disp)
    (Obj : I -> algType R)
    (bonding : forall i j, i <= j -> {lrmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isAlgebraDirLim R _ _ _ _ Sys dlT.

Implicit Type (x y : dlT) (r : R).

HB.instance Definition _ :=
  DirLim_isLalgDirLim.Build R _ _ _ _ Sys dlT.

Fact dlscaleAr r x y : r *: (x * y) = x * (r *: y).
Proof.
have [i u v <-{x} <-{y}] := dirlim2P x y.
by rewrite -[r *: _ v]linearZ /= -!rmorphM /= -linearZ /= -scalerAr.
Qed.
HB.instance Definition _ :=
  GRing.Lalgebra_isAlgebra.Build R dlT dlscaleAr.

HB.end.


Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for direct limits                             *)
(*                                                                         *)
(***************************************************************************)
Open Scope quotient_scope.

Section Implem.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Definition dirlim := {eq_quot (dsyseq Sys)}.
Definition dlinj_impl i (u : Obj i) := \pi_dirlim (DPair u).

HB.instance Definition _ := Choice.on dirlim.

End Implem.
Notation "{ 'dirlim' S }" := (dirlim S).


Section DirectLimitTheory.

Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Implicit Type (i j k : I) (x y : {dirlim Sys}).

Lemma dsyseq_dlinj_impl i (u : Obj i) :
  dsyseq Sys (DPair u) (repr (dlinj_impl Sys u)).
Proof. by have [v /eqmodP] := piP {dirlim Sys} (DPair u). Qed.

(** Budlding the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Obj i -> T).

Definition dlind_impl of cocone Sys f := fun x => f (projT2 (repr x)).

Hypothesis Hcone : cocone Sys f.

Lemma dlind_implP i (u : Obj i) : dlind_impl Hcone (dlinj_impl Sys u) = f u.
Proof.
rewrite /dlind_impl; apply (dsyseqE Hcone); rewrite dsyseq_sym /=.
by case: (repr _) (dsyseq_dlinj_impl u).
Qed.

Lemma dlind_implE i j (u : Obj i) (v : Obj j) :
  dsyseq Sys (DPair u) (DPair v) ->
  dlind_impl Hcone (dlinj_impl Sys  u) = dlind_impl Hcone (dlinj_impl Sys  v).
Proof. by rewrite !dlind_implP => /(dsyseqE Hcone). Qed.

End UniversalProperty.

Fact dlinj_implP : cocone Sys (dlinj_impl Sys).
Proof.
rewrite /dlinj_impl => i j le_ij u /=.
apply/eqmodP; rewrite /= dsyseq_sym.
exact: dsyseq_bonding.
Qed.

Lemma dlind_impl_commute
  T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) i :
  dlind_impl Hcone \o (dlinj_impl Sys) i =1 f i.
Proof. by move=> x /=; rewrite dlind_implP. Qed.

Lemma dlind_impl_uniq
  T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) (ind : {dirlim Sys} -> T) :
  (forall i, ind \o (dlinj_impl Sys) i =1 f i) ->
  ind =1 dlind_impl Hcone.
Proof.
move=> H /= x; rewrite /dlind_impl /=.
suff {1}-> : x = dlinj_impl Sys (projT2 (repr x)).
  exact: H (projT1 (repr x)) (projT2 (repr x)).
rewrite -{1}(reprK x) /= /dlinj_impl /=.
by case: (repr x).
Qed.
HB.instance Definition _ :=
  @isDirLim.Build disp I Obj bonding Sys {dirlim Sys}
    _ _ dlinj_implP dlind_impl_commute dlind_impl_uniq.

End DirectLimitTheory.

Open Scope ring_scope.

Section Instances.

Variables (disp : unit) (I : dirType disp).

Section NModule.
Variable Obj : I -> nmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := DirLim_isNmodDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End NModule.

Section ZModule.
Variable Obj : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := DirLim_isZmodDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End ZModule.

Section SemiRing.
Variable Obj : I -> semiRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isSemiRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End SemiRing.

Section Ring.
Variable Obj : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := DirLim_isRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End Ring.

Section ComSemiRing.
Variable Obj : I -> comSemiRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isComSemiRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End ComSemiRing.

Section ComRing.
Variable Obj : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := DirLim.on {dirlim Sys}.
Let test : comRingDirLimType _ := {dirlim Sys}.
End ComRing.

Section UnitRing.
Variable Obj : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isUnitRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End UnitRing.

Section ComUnitRing.
Variable Obj : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := GRing.ComRing.on {dirlim Sys}.
Let test : comUnitRingDirLimType _ := {dirlim Sys}.
End ComUnitRing.

Section Linear.
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isLmoduleDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isLalgDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isAlgebraDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Obj : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := GRing.Algebra.on {dirlim Sys}.
End UnitAlg.

Section ComAlg.
Variables (R : comRingType).
Variable Obj : I -> comAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := GRing.Algebra.on {dirlim Sys}.
End ComAlg.

Section ComUnitAlg.
Variables (R : comRingType).
Variable Obj : I -> comUnitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := GRing.Algebra.on {dirlim Sys}.
End ComUnitAlg.

Section IDomain.
Variable Obj : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isIDomainDirLim.Build _ _ _ _ Sys {dirlim Sys}.
Let test : idomainDirLimType _ := {dirlim Sys}.
End IDomain.

Section Field.
Variable Obj : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isFieldDirLim.Build _ _ _ _ Sys {dirlim Sys}.
Let test : fieldDirLimType _ := {dirlim Sys}.
End Field.

End Instances.


Section TestComUnitAlg.
Variable (R : comRingType).
Variables (disp : unit) (I : dirType disp).
Variable Obj : I -> comUnitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Let test1 : algDirLimType _ := {dirlim Sys}.
Let test2 : comUnitRingDirLimType _ := {dirlim Sys}.
End TestComUnitAlg.
