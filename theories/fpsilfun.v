(** Formal power series *)
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

Require Import natbar invlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Def.
Import Order.Syntax.
Import Order.Theory.

Require Import auxresults truncps invlim.

Reserved Notation "{ 'series' R }"
         (at level 0, R at level 2, format "{ 'series'  R }").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\series E .X^ i"
  (at level 36, E at level 36, i at level 50, format "\series  E  .X^ i").
Reserved Notation "''X" (at level 0).
Reserved Notation "'''X^' n" (at level 3, n at level 2, format "'''X^' n").
Reserved Notation "a ^`` ()" (at level 8, format "a ^`` ()").
Reserved Notation "s ``_ i" (at level 3, i at level 2, left associativity,
                            format "s ``_ i").


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.


Section Defs.

Variable R : ringType.

Definition fps_bond := fun (i j : nat) of (i <= j)%O => @trXnt R j i.

Section Canonical.

Variables (i j : nat) (le_ij : (i <= j)%O).
Lemma bond_is_rmorphism : rmorphism (fps_bond le_ij).
Proof.
split; first exact: trXnt_is_linear.
rewrite /fps_bond; apply trXnt_is_multiplicative.
by rewrite -leEnat.
Qed.
Canonical bond_additive := Additive bond_is_rmorphism.
Canonical bond_rmorphism := RMorphism bond_is_rmorphism.

Lemma bond_is_linear : linear (fps_bond le_ij).
Proof. exact: trXnt_is_linear. Qed.
Canonical bond_linear := AddLinear bond_is_linear.
Canonical bond_lrmorphism := [lrmorphism of (fps_bond le_ij)].

End Canonical.

Program Definition fps_invsys :=
  InvSys (bonding :=
            fun i j (le_ij : (i <= j)%O) => [lrmorphism of fps_bond le_ij])
         0%N _ _.
Next Obligation. exact: trXnt_id. Qed.
Next Obligation.
by move=> f /=; rewrite /fps_bond; apply: trXnt_trXnt; rewrite -leEnat.
Qed.


(* I'd rather not add a coercion here ! It is redundant with the
   notation p``_i which is very confusing *)
Record fpseries := FPSeries { seriesfun : nat -> R }.

Canonical fpseries_eqType := EqType fpseries gen_eqMixin.
Canonical fpseries_choiceType := ChoiceType fpseries gen_choiceMixin.

Lemma seriesfun_inj : injective seriesfun.
Proof. by move=> [f1] [f2] /= ->. Qed.

Definition fpseries_of of phant R := fpseries.
Identity Coercion type_fpseries_of : fpseries_of >-> fpseries.

Definition coef_series_def (s : fpseries_of (Phant R)) i := seriesfun s i.
Fact coef_series_key : unit. Proof. by []. Qed.
Definition coef_series := locked_with coef_series_key coef_series_def.
Canonical coef_series_unlockable := [unlockable fun coef_series].
Definition coefps_head h i (s : fpseries_of (Phant R)) :=
  let: tt := h in coef_series s i.

Local Notation "{ 'series' R }" := (fpseries_of (Phant R)).
Local Notation coefs i := (coefps_head tt i).
Local Notation "s ``_ i" := (coef_series s i).

Lemma coefs_FPSeries (f : nat -> R) i : (FPSeries f)``_i = f i.
Proof. by rewrite unlock. Qed.

Definition fpsproj n (f : {series R}) : {tfps R n} := [tfps i <= n => f``_i].

Lemma fpsprojP : iscompat fps_invsys fpsproj.
Proof.
rewrite /fps_bond /= => i j; rewrite leEnat => le_ij f /=.
apply tfpsP=> k le_ki.
by rewrite coef_trXnt le_ki !coef_tfps_of_fun le_ki (leq_trans le_ki le_ij).
Qed.

Local Notation "''pi_' i" := (fpsproj i).

Lemma fpsprojE x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
rewrite /fpsproj => eqxy; apply/seriesfun_inj/funext => i.
have:= congr1 (fun t : {tfps R i} => t`_i) (eqxy i).
by rewrite !coef_tfps_of_fun leqnn unlock.
Qed.

(** Building the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, T -> {tfps R i}).
Definition fpsind (_ : iscompat fps_invsys f) t : {series R} :=
  FPSeries (fun i => (f i t)`_i).

Hypothesis Hcomp : iscompat fps_invsys f.
Lemma fpsindP i t : 'pi_i (fpsind Hcomp t) = f i t.
Proof.
rewrite /fpsind /=; apply tfpsP => j le_ji /=.
rewrite coef_tfps_of_fun le_ji coefs_FPSeries.
rewrite -leEnat in le_ji; rewrite -(Hcomp le_ji) /=.
by rewrite /fps_bond coef_trXnt leqnn.
Qed.

Lemma fpsindE (un : T -> {series R}) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 (fpsind Hcomp).
Proof.
move=> eqproj x; apply fpsprojE => i.
by rewrite -/(('pi_i \o un) _) eqproj fpsindP.
Qed.

End UniversalProperty.

Program Definition fps_invlim_Mixin :=
  @InvLimMixin _ nat_dirType _ fps_bond fps_invsys {series R}
               fpsproj fpsind _ _ _.
Next Obligation. by move=> i j le_ij x; apply: fpsprojP. Qed.
Next Obligation. by move=> x /=; rewrite fpsindP. Qed.
Next Obligation. by move=> x; apply: (fpsindE Hcomp). Qed.
Canonical fps_invlimType := InvLimType {series R} fps_invlim_Mixin.

Canonical fps_zmodType :=
  Eval hnf in ZmodType {series R} [zmodMixin of {series R} by <-].

(*
Definition fps_ringMixin := [ringMixin of {series R} by <-].

Canonical fps_ringType :=
  Eval hnf in RingType {series R} [ringMixin of {series R} by <-].
*)
End Defs.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with fpseries_of.
Bind Scope ring_scope with fpseries.

Arguments seriesfun {R} f%R.
Arguments seriesfun_inj {R} [s1%R s2%R] : rename.
Arguments coefps_head {R} h i%N s%R.
Arguments coef_series {R} s%R i%N.

Notation "{ 'series' T }" := (fpseries_of (Phant T)).
Notation coefs i := (coefps_head tt i).
Notation "s ``_ i" := (coef_series s i).


Section Debug.

Variable R : ringType.

Check [ringMixin of {series R} by <-].


Check (InvLimitRing.invlim_ringMixin (Phant {series R})).

Definition fps_ringMixin (R : ringType) := [ringMixin of {series R} by <-].


Section CoeffSeries.

Variable R : ringType.

Implicit Types (a b c: R) (s t u : {series R}) (p q : {poly R}) (i j : nat).

Lemma coefs_piE i s : s``_i = ('pi_i s)`_i.
Proof. by rewrite coef_tfps_of_fun leqnn. Qed.

Lemma coefs_pi_leqE i j : (i <= j)%N -> forall s, s``_i = ('pi_j s)`_i.
Proof.
rewrite -leEnat => H s.
by rewrite coefs_piE -(ilprojE s H) /fps_bond coef_trXn leqnn.
Qed.

Lemma coefsE i s : coefs i s = s``_i.
Proof. by []. Qed.

Lemma coefs0 i : (0 : {series R })``_i = 0.
Proof. by rewrite coefs_piE raddf0 coef0. Qed.

Lemma coefs1 i : (1 : {series R })``_i = (i == 0%N)%:R.
Proof. by rewrite coefs_piE rmorph1 coef1. Qed.

Lemma seriesP s t : (forall n, s``_n = t``_n) <-> (s = t).
Proof.
split => [Hco|-> //]; apply/invlimP => /= i.
apply/tfpsP => j le_ji.
by rewrite -!(coefs_pi_leqE le_ji) Hco.
Qed.


Lemma coefs_is_additive i : additive (@coefps_head R tt i).
Proof. by move=> s t; rewrite !coefsE !coefs_piE !raddfB coefB. Qed.
Canonical coefs_additive i : {additive {series R} -> R} :=
  Additive (coefs_is_additive i).

Lemma coefsD s t i : (s + t)``_i = s``_i + t``_i.
Proof. exact: (raddfD (coefs_additive i)). Qed.
Lemma coefsN s i : (- s)``_i = - (s``_i).
Proof. exact: (raddfN (coefs_additive i)). Qed.
Lemma coefsB s t i : (s - t)``_i = s``_i - t``_i.
Proof. exact: (raddfB (coefs_additive i)). Qed.
Lemma coefsMn s n i : (s *+ n)``_i = (s``_i) *+ n.
Proof. exact: (raddfMn (coefs_additive i)). Qed.
Lemma coefsMNn s n i : (s *- n)``_i = (s``_i) *- n.
Proof. by rewrite coefsN coefsMn. Qed.
Lemma coefs_sum I (r : seq I) (s : pred I) (F : I -> {series R}) k :
  (\sum_(i <- r | s i) F i)``_k = \sum_(i <- r | s i) (F i)``_k.
Proof. exact: (raddf_sum (coefs_additive k)). Qed.


Lemma isthreadC c : isthread (fps_invsys R) (fun i => c%:S%tfps).
Proof. by move=> i j Hij; rewrite /fps_bond /= trXntC. Qed.
(* Definition seriesC c : {series R} := InvLim (isthreadC c). *)
Definition seriesC c : {series R} := ilthr (isthreadC c).
Local Notation "c %:S" := (seriesC c).

Lemma coefsC c i : c%:S``_i = (if i == 0%N then c else 0).
Proof. by rewrite coefs_piE invLimP coef_tfpsC. Qed.

Lemma series0E : 0%:S = 0.
Proof. by apply/seriesP => i; rewrite coefs0 coefsC; case eqP. Qed.
Lemma series1E : 1%:S = 1.
Proof. by apply/seriesP => i; rewrite coefs1 coefsC; case eqP. Qed.

Lemma seriesC_eq0 (c : R) : (c%:S == 0) = (c == 0).
Proof.
apply/eqP/eqP => [/(congr1 (coefs 0%N))|->]; last exact: series0E.
by rewrite /= coefs0 coefsC.
Qed.

Lemma seriesCB : {morph seriesC : a b / a + b}.
Proof.
by move=> a b; apply/seriesP=>[[|i]]; rewrite coefsD !coefsC ?addr0. Qed.
Lemma seriesCN : {morph seriesC : c / - c}.
Proof. by move=> c; apply/seriesP=> [[|i]]; rewrite coefsN !coefsC ?oppr0. Qed.
Lemma seriesCD : {morph seriesC : a b / a - b}.
Proof. by move=> a b; rewrite seriesCB seriesCN. Qed.

Canonical seriesC_additive := Additive seriesCD.

Lemma seriesCMn n : {morph seriesC : c / c *+ n}.
Proof. exact: raddfMn. Qed.
Lemma seriesCMNn n : {morph seriesC : c / c *- n}.
Proof. exact: raddfMNn. Qed.
Lemma seriesC_sum I (r : seq I) (s : pred I) (F : I -> R) :
  (\sum_(i <- r | s i) F i)%:S = \sum_(i <- r | s i) (F i)%:S.
Proof. exact: raddf_sum. Qed.


Lemma isthread_poly (p : {poly R}) :
  isthread (fps_invsys R) (fun n => trXn n p).
Proof. by move=> i j Hij; rewrite /fps_bond /trXnt /= trXn_trXn. Qed.
Definition series_poly (p : {poly R}) : {series R} := ilthr (isthread_poly p).

Lemma coefs_series_poly p i : (series_poly p)``_i = p`_i.
Proof. by rewrite coefs_piE invLimP coef_trXn leqnn. Qed.

Lemma series_polyK n p :
  (n >= size p)%N -> tfps ('pi_n (series_poly p)) = p.
Proof.
move=> Hn; apply/polyP => i; case: (leqP i n) => [le_in|lt_ni].
- by rewrite -[LHS](coefs_pi_leqE le_in) coefs_series_poly.
- by rewrite coef_tfps leqNgt lt_ni [RHS]nth_default ?(leq_trans Hn (ltnW _)).
Qed.

Lemma series_poly_inj : injective series_poly.
Proof.
move=> p q /(congr1 ('pi_(maxn (size p) (size q))))/(congr1 tfps).
by rewrite !series_polyK ?leq_maxr ?leq_maxl.
Qed.


Fact series_poly_is_additive : additive series_poly.
Proof.
move=> p q; apply/seriesP => n.
by rewrite coefsB !coefs_piE !invLimP raddfB /= coeftB /=.
Qed.
Canonical series_poly_additive := Additive series_poly_is_additive.

Lemma series_polyD p q : series_poly (p + q) = series_poly p + series_poly q.
Proof. exact: raddfD. Qed.
Lemma series_polyN p : series_poly (- p) = - series_poly p.
Proof. exact: raddfN. Qed.
Lemma series_polyB p q : series_poly (p - q) = series_poly p - series_poly q.
Proof. exact: raddfB. Qed.
Lemma series_polyMn p n : series_poly (p *+ n) = (series_poly p) *+ n.
Proof. exact: raddfMn. Qed.
Lemma series_polyMNn p n : series_poly (p *- n) = (series_poly p) *- n.
Proof. exact: raddfMNn. Qed.
Lemma series_poly_sum I (r : seq I) (s : pred I) (F : I -> {poly R}) :
  series_poly (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) series_poly (F i).
Proof. exact: raddf_sum. Qed.


Lemma poly_series_eqP s t :
  (forall n, 'pi_n s = 'pi_n t) <-> (s = t).
Proof. by split => [|-> //]; apply: invlimP. Qed.

Lemma poly_seriesC n c : tfps ('pi_n c%:S) = c%:P :> {poly R}.
Proof. by apply/polyP => i; rewrite invLimP coef_tfpsC coefC. Qed.

Lemma series_polyC c : series_poly c%:P = c%:S.
Proof. by apply/seriesP => n; rewrite coefs_series_poly coefC coefsC. Qed.


Lemma isthread_from_fun (f : nat -> R) :
  isthread (fps_invsys R) (fun n => [tfps i <= n => f i ]%tfps).
Proof.
Proof.
move=> i j le_ij; rewrite /fps_bond /trXnt.
apply/tfpsP => k le_ki.
by rewrite coef_trXn !coef_tfps_of_fun le_ki (leq_trans le_ki le_ij).
Qed.
Definition series_from_fun f : {series R} := MkInvLim (isthread_from_fun f).

Local Notation "\series E .X^ i" := (series_from_fun (fun i : nat => E)).

Lemma coefs_series E j : (\series E i .X^i)``_j = E j.
Proof. by rewrite /series_from_fun unlock /= coef_poly ltnSn. Qed.


Fact coefsM s t i : (s * t)``_i = \sum_(j < i.+1) s``_j * t``_(i - j).
Proof.
rewrite coefs_piE invLimP /= coefM_tfps leqnn.
apply eq_bigr => [[j]] /=; rewrite ltnS => le_ji _.
by rewrite -!coefs_pi_leqE ?leq_subr.
Qed.
Lemma coefsMr s t n : (s * t)``_n = \sum_(j < n.+1) s``_(n - j) * t``_j.
Proof.
rewrite coefs_piE invLimP /= coefMr_tfps leqnn.
apply eq_bigr => [[j]] /=; rewrite ltnS => le_ji _.
by rewrite -?coefs_pi_leqE ?leq_subr.
Qed.

Fact coefs0_multiplicative : multiplicative (coefs 0 : {series R} -> R).
Proof.
split=> [s t|] /=; last by rewrite coefs1.
by rewrite coefsM big_ord_recl big_ord0 addr0 /= subnn.
Qed.
Canonical coefs0_rmorphism := AddRMorphism coefs0_multiplicative.


Fact series_poly_is_rmorphism : rmorphism series_poly.
Proof.
split; first exact: series_poly_is_additive.
split=> [p q|]; apply/seriesP=> i; first last.
  by rewrite !coefs_piE !invLimP /= trXn1.
rewrite coefs_series_poly coefM coefsM; apply: eq_bigr => j _.
by rewrite !coefs_series_poly.
Qed.
Canonical series_poly_rmorphism := RMorphism series_poly_is_rmorphism.

Lemma series_polyX n : {morph series_poly : p / p ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma series_poly1 : series_poly 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma series_polyM : {morph series_poly : x y  / x * y}.
Proof. exact: rmorphM. Qed.

Lemma mul_seriesC a s : a%:S * s = a *: s.
Proof.
apply/poly_series_eqP => i.
by rewrite linearZ /= !invLimP -alg_tfpsC mulr_algl.
Qed.

Lemma coefsZ a s i : (a *: s)``_i = a * s``_i.
Proof. by rewrite !coefs_piE linearZ coefZ. Qed.

Lemma alg_seriesC a : a%:A = a%:S :> {series R}.
Proof. by rewrite -mul_seriesC mulr1. Qed.

Canonical coefps_linear i : {scalar {series R}} :=
  AddLinear ((fun a => (coefsZ a) ^~ i) : scalable_for *%R (coefs i)).
Canonical coefp0_lrmorphism := [lrmorphism of coefs 0].


Fact series_poly_is_scalable : scalable series_poly.
Proof.
move=> c p; apply/seriesP => n.
by rewrite coefsZ !coefs_series_poly coefZ.
Qed.
Canonical series_poly_linear := AddLinear series_poly_is_scalable.
Canonical series_poly_lrmorphism := [lrmorphism of series_poly].


Local Notation "''X" := (locked (@series_poly 'X)).
Local Notation "'''X^' n" := (''X ^+ n).

Lemma seriesXE n : 'pi_n ''X = (\X)%tfps.
Proof. by rewrite -lock invLimP. Qed.
Lemma seriesXnE n i : 'pi_n ''X^i = (\X)%tfps^+i.
Proof. by rewrite !rmorphX /= seriesXE. Qed.
Lemma coefsX i : (''X ``_i) = (i == 1%N)%:R :> R.
Proof. by rewrite -lock coefs_series_poly coefX. Qed.
Lemma coefsXn n i : (''X^n ``_i) = (i == n)%:R :> R.
Proof. by rewrite -lock -rmorphX /= coefs_series_poly coefXn. Qed.

Lemma seriesX_eq0 : (''X == 0 :> {series R}) = false.
Proof.
apply/negP => /eqP/seriesP/(_ 1%N)/eqP.
by rewrite coefsX coefs0 /= oner_eq0.
Qed.

Lemma commr_seriesX s : GRing.comm s ''X.
Proof.
apply/seriesP=> i; rewrite coefsMr coefsM.
by apply: eq_bigr => j _; rewrite coefsX commr_nat.
Qed.

Lemma commr_seriesXn n s : GRing.comm s ''X^n.
Proof. exact/commrX/commr_seriesX. Qed.


End CoeffSeries.

Coercion series_poly : poly_of >-> fpseries_of.

Arguments seriesC {R}.
Arguments series_poly {R}.
Notation "c %:S" := (seriesC c).
Notation "\series E .X^ i" := (series_from_fun _ (fun i : nat => E)).

