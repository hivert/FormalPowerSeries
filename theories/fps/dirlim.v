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

Require Import natbar directed dirlim_constr.


Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(***************************************************************************)
(** Direct systems and direct limits                                       *)
(*                                                                         *)
(***************************************************************************)

#[key="dlT"]
HB.factory Record isDirLim_classical
    disp (I : dirType disp)
    (Obj : I -> Type) (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  dlT of Choice dlT := {
    dirlim_inj i : Obj i -> dlT;
    dirlim_ind T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) : dlT -> T;
    dlinjP : cocone Sys dirlim_inj;
    dlind_commute T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) :
      forall i, dirlim_ind T f Hcone \o dirlim_inj i =1 f i;
    dlind_uniq T (f : forall i, Obj i -> T) (Hcone : cocone Sys f) :
      forall (ind : dlT -> T),
        (forall i, ind \o dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind T f Hcone
  }.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> Type) (bonding : forall i j, i <= j -> Obj i -> Obj j)
    (Sys : is_dirsys bonding)
  dlT of isDirLim_classical disp I Obj bonding Sys dlT.

Lemma cocone_dsyseq u :
  cocone Sys (fun j (v : Obj j) => `[< dsysequal Sys u (existT Obj j v) >]).
Proof.
move=> j k le_jk v /=.
case: (boolP `[< dsysequal Sys u (existT Obj j v) >]) => /asboolP.
- move=> [l /= le_il le_jl Hbond]; apply/asboolP.
  have [m le_km le_lm] := directedP k l.
  apply: (Dsysequal (le_trans le_il le_lm)) => /=.
  rewrite -(dirsys_comp Sys le_il le_lm) /= Hbond.
  by rewrite !bonding_transE //; apply: bondingE.
- move=> Hnthr; apply/asboolF => /= [] [l /= le_il le_kl].
  rewrite bonding_transE // => Hbond; apply: Hnthr.
  apply: (Dsysequal le_il) => /=; first exact: le_trans le_jk le_kl.
  by move => le_jl; rewrite Hbond; apply: bondingE.
Qed.

Lemma dirlim_eq i (u : Obj i) j (v : Obj j) :
  dirlim_inj u = dirlim_inj v ->
  exists k (leik : i <= k) (lejk : j <= k),
    bonding i k leik u = bonding j k lejk v.
Proof.
move=> eqinj.
apply contrapT; rewrite -forallNP => Hbond.
have Hcone := cocone_dsyseq (existT Obj j v).
have /= := dlind_commute Hcone v; rewrite -eqinj.
have /= -> := dlind_commute Hcone u.
move=> H; have {H} [_] := asbool_eq_equiv H.
move=> /(_ (dsysequal_refl _ (existT Obj j v))) [k le_jk le_ik Habs].
apply: (Hbond k); exists (le_ik); exists (le_jk); rewrite Habs.
exact: bondingE.
Qed.

Lemma dirlim_surj (x : dlT) : exists i (u : Obj i), dirlim_inj u = x.
Proof.
rewrite not_existsP => H.
pose f i := pred0 (T := Obj i).
have Hcone : cocone Sys f by [].
have /(@dlind_uniq _ _ Hcone)/(_ x) :
  forall i, (pred0 (T := dlT)) \o dirlim_inj (i:=i) =1 f i by [].
suff /(@dlind_uniq _ _ Hcone)/(_ x) <- :
  forall i, (pred1 x) \o dirlim_inj (i:=i) =1 f i.
  by rewrite /= eqxx.
rewrite /f => i u /=; apply/negP => /eqP eq_inj.
by apply/(H i); exists u.
Qed.

HB.instance Definition _ :=
  isDirLim.Build disp I Obj bonding Sys dlT
    dirlim_eq dirlim_surj dlinjP dlind_commute dlind_uniq.

HB.end.


Section DirSysCongr.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> Type.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Definition dsyseq (Sys : is_dirsys bonding) u v := `[< dsysequal Sys u v >].

Lemma dsyseqP u v : reflect (dsysequal Sys u v) (dsyseq Sys u v).
Proof. exact: asboolP. Qed.

Lemma dsyseq_bonding i j (le_ij : i <= j) (u : Obj i) :
  dsyseq Sys (existT Obj i u) (existT Obj j (bonding le_ij u)).
Proof.
apply/dsyseqP; apply: (Dsysequal (k := j)) => /=.
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dsyseq_refl u : dsyseq Sys u u.
Proof. exact/dsyseqP/dsysequal_refl. Qed.
Lemma dsyseq_sym u v : dsyseq Sys u v = dsyseq Sys v u.
Proof. by apply/dsyseqP/dsyseqP; rewrite dsysequal_sym. Qed.
Lemma dsyseq_trans : transitive (dsyseq Sys).
Proof. by move=> v u w /dsyseqP/dsysequal_trans H /dsyseqP{}/H/dsyseqP. Qed.
Canonical SysEq :=
  EquivRel (@dsyseq Sys) dsyseq_refl dsyseq_sym dsyseq_trans.

Lemma cocone_dsyseq u :
  cocone Sys (fun j (v : Obj j) => dsyseq Sys u (existT Obj j v)).
Proof.
move=> j k le_jk v /=.
case: (boolP (dsyseq Sys u (existT Obj j v))) => [/dsyseqP | /dsyseqP Hnthr].
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

Variable dlT : dirLimType Sys.
Implicit Type (x y z : dlT).

Lemma dsyseqE i j (u : Obj i) (v : Obj j) :
  ('inj[dlT] u == 'inj[dlT] v) = (dsyseq Sys (existT Obj i u) (existT Obj j v)).
Proof. exact/dirlimE/dsyseqP. Qed.

End DirSysCongr.
Arguments dsyseq {disp I Obj bonding} (Sys) (u v).


(****************************************************************************)
(** Canonical structures for inverse limits in various algebraic categories *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)
Open Scope ring_scope.


HB.factory Record DirLim_isUnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> unitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isUnitRingDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isNmoduleDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  NmoduleDirLim_isSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  SemiRingDirLim_isRingDirLim.Build _ _ _ _ Sys dlT.

Definition dlunit x :=
  `[< exists p : {i & Obj i},
        ('inj[dlT] (projT2 p) == x) && (projT2 p \is a GRing.unit) >].

Fact dlunit_decP x : reflect
  (exists i (u : Obj i), 'inj[dlT] u = x /\ u \is a GRing.unit) (dlunit x).
Proof.
apply (iffP (asboolP _)) => [[inv /andP[/eqP {x}<- Hunit]] | [i][inv] [Heq Hunit]].
  by exists (tag inv); exists (projT2 inv).
by exists (existT _ i inv); rewrite Heq eqxx.
Qed.

HB.instance Definition _ :=
  RingDirLim_isUnitRingDirLim.Build _ _ _ _ Sys dlT dlunit_decP.

HB.end.


HB.factory Record DirLim_isComUnitRingDirLim
    disp (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> comUnitRingType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isComUnitRingDirLim _ _ _ _ Sys dlT.

HB.instance Definition _ := DirLim_isUnitRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  SemiRingDirLim_isComSemiRingDirLim.Build _ _ _ _ Sys dlT.
HB.end.


HB.factory Record DirLim_isIDomainDirLim
    disp (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> idomainType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isIDomainDirLim _ _ _ _ Sys dlT.

Implicit Type x y : dlT.

HB.instance Definition _ :=
  DirLim_isComUnitRingDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  ComUnitRingDirLim_isIntegralDirLim.Build _ _ _ _ Sys dlT.

HB.end.


HB.factory Record DirLim_isFieldDirLim
    disp (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim _ Sys dlT := {}.
HB.builders Context
    disp (I : dirType disp)
    (Obj : I -> fieldType)
    (bonding : forall i j, i <= j -> {rmorphism Obj i -> Obj j})
    (Sys : is_dirsys bonding)
  dlT of DirLim_isFieldDirLim _ _ _ _ Sys dlT.

HB.instance Definition _ :=
  DirLim_isIDomainDirLim.Build _ _ _ _ Sys dlT.
HB.instance Definition _ :=
  IDomainDirLim_isFieldDirLim.Build _ _ _ _ Sys dlT.

HB.end.

Close Scope ring_scope.


(***************************************************************************)
(** A default implementation for direct limits                             *)
(*                                                                         *)
(***************************************************************************)
Open Scope quotient_scope.

Section Implem.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Definition dirlim := {eq_quot (dsyseq Sys)}.
Definition dlinj_impl i (u : Obj i) := \pi_dirlim (existT Obj i u).

HB.instance Definition _ := Choice.on dirlim.

End Implem.
Notation "{ 'dirlim' S }" := (dirlim S).


Section DirectLimitTheory.

Variables (disp : _) (I : dirType disp).
Variable Obj : I -> choiceType.
Variable bonding : forall i j, i <= j -> Obj i -> Obj j.
Variable Sys : is_dirsys bonding.

Implicit Type (i j k : I) (x y : {dirlim Sys}).

Lemma dsyseq_dlinj_impl i (u : Obj i) :
  dsyseq Sys (existT Obj i u) (repr (dlinj_impl Sys u)).
Proof. by have [v /eqmodP] := piP {dirlim Sys} (existT Obj i u). Qed.

(** Budlding the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Obj i -> T).

Definition dlind_impl of cocone Sys f := fun x => f (projT2 (repr x)).

Hypothesis Hcone : cocone Sys f.

Lemma dlind_implP i (u : Obj i) : dlind_impl Hcone (dlinj_impl Sys u) = f u.
Proof.
rewrite /dlind_impl; apply/(dsysequalE Hcone)/dsyseqP; rewrite dsyseq_sym /=.
by case: (repr _) (dsyseq_dlinj_impl u).
Qed.

Lemma dlind_implE i j (u : Obj i) (v : Obj j) :
  dsyseq Sys (existT Obj i u) (existT Obj j v) ->
  dlind_impl Hcone (dlinj_impl Sys  u) = dlind_impl Hcone (dlinj_impl Sys  v).
Proof. by rewrite !dlind_implP => /dsyseqP/(dsysequalE Hcone). Qed.

End UniversalProperty.

Fact dlinj_implP : cocone Sys (dlinj_impl Sys).
Proof.
rewrite /dlinj_impl => i j le_ij u /=.
apply/eqmodP; rewrite /= dsyseq_sym.
exact: dsyseq_bonding.
Qed.

Lemma dlind_impl_commute
  (T : Type) (f : forall i, Obj i -> T) (Hcone : cocone Sys f) i :
  dlind_impl Hcone \o (dlinj_impl Sys) i =1 f i.
Proof. by move=> x /=; rewrite dlind_implP. Qed.

Lemma dlind_impl_uniq
  (T : Type) (f : forall i, Obj i -> T) (Hcone : cocone Sys f)
  (ind : {dirlim Sys} -> T) :
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
  @isDirLim_classical.Build disp I Obj bonding Sys {dirlim Sys}
    _ _ dlinj_implP dlind_impl_commute dlind_impl_uniq.

End DirectLimitTheory.

Open Scope ring_scope.

Section Instances.

Variables (disp : _) (I : dirType disp).

Section NModule.
Variable Obj : I -> nmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  DirLim_isNmoduleDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End NModule.

Section ZModule.
Variable Obj : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  NmoduleDirLim_isZmoduleDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End ZModule.

Section SemiRing.
Variable Obj : I -> semiRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  NmoduleDirLim_isSemiRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End SemiRing.

Section Ring.
Variable Obj : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  SemiRingDirLim_isRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End Ring.

Section ComSemiRing.
Variable Obj : I -> comSemiRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  SemiRingDirLim_isComSemiRingDirLim.Build _ _ _ _ Sys {dirlim Sys}.
End ComSemiRing.

Section ComRing.
Variable Obj : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ := DirLim.on {dirlim Sys}.
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

Section Linear.
Variables (R : ringType).
Variable Obj : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  ZmoduleDirLim_isLmoduleDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Obj : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  LmoduleDirLim_isLalgebraDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Obj : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
HB.instance Definition _ :=
  LalgebraDirLim_isAlgebraDirLim.Build R _ _ _ _ Sys {dirlim Sys}.
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

End Instances.


Section TestComUnitAlg.
Variable (R : comRingType).
Variables (disp : _) (I : dirType disp).
Variable Obj : I -> comUnitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Obj i -> Obj j}.
Variable Sys : is_dirsys bonding.
Let test1 : algDirLimType _ := {dirlim Sys}.
Let test2 : comUnitRingDirLimType _ := {dirlim Sys}.
End TestComUnitAlg.
