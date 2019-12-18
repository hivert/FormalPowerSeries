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

Reserved Notation "{ 'fps' R }"
         (at level 0, R at level 2, format "{ 'fps'  R }").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\fps E .X^ i"
  (at level 36, E at level 36, i at level 50, format "\fps  E  .X^ i").
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


Fact fps_bond_key : unit. Proof. by []. Qed.
Definition fps_bond :=
  locked_with fps_bond_key (fun (i j : nat) of (i <= j)%O => @trXnt R j i).
Canonical fps_bond_unlockable := Eval hnf in [unlockable fun fps_bond].

Section Canonical.

Variables (i j : nat) (le_ij : (i <= j)%O).

Lemma fps_bondE f : fps_bond le_ij f = trXnt i f.
Proof. by rewrite unlock. Qed.

Lemma bond_is_rmorphism : rmorphism (fps_bond le_ij).
Proof.
rewrite unlock; split; first exact: trXnt_is_linear.
rewrite /fps_bond; apply trXnt_is_multiplicative.
by rewrite -leEnat.
Qed.
Canonical bond_additive : {additive {tfps R j} -> {tfps R i}} :=
  Eval hnf in Additive bond_is_rmorphism.
Canonical bond_rmorphism : {rmorphism {tfps R j} -> {tfps R i}} :=
  Eval hnf in RMorphism bond_is_rmorphism.

Lemma bond_is_linear : linear (fps_bond le_ij).
Proof. by rewrite unlock; exact: trXnt_is_linear. Qed.
Canonical bond_linear : {linear {tfps R j} -> {tfps R i}} :=
  Eval hnf in AddLinear bond_is_linear.
Canonical bond_lrmorphism : {lrmorphism {tfps R j} -> {tfps R i}} :=
  Eval hnf in [lrmorphism of (fps_bond le_ij)].

End Canonical.


Program Definition fps_invsys :=
  InvSys (bonding := fun (i j : nat) (le_ij : (i <= j)%O) => fps_bond le_ij)
         0%N _ _.
Next Obligation. by rewrite unlock; exact: trXnt_id. Qed.
Next Obligation.
by move=> f /=; rewrite unlock; apply: trXnt_trXnt; rewrite -leEnat.
Qed.


(* I'd rather not add a coercion here ! It is redundant with the
   notation p``_i which is very confusing *)
Record fpseries := FPSeries { seriesfun : nat -> R }.

Canonical fpseries_eqType := Eval hnf in EqType fpseries gen_eqMixin.
Canonical fpseries_choiceType :=
  Eval hnf in ChoiceType fpseries gen_choiceMixin.

Lemma seriesfun_inj : injective seriesfun.
Proof. by move=> [f1] [f2] /= ->. Qed.

Definition fpseries_of of phant R := fpseries.
Identity Coercion type_fpseries_of : fpseries_of >-> fpseries.

Definition coef_series_def (s : fpseries_of (Phant R)) i := seriesfun s i.
Fact coef_series_key : unit. Proof. by []. Qed.
Definition coef_series := locked_with coef_series_key coef_series_def.
Canonical coef_series_unlockable :=
  Eval hnf in [unlockable fun coef_series].
Definition coefps_head h i (s : fpseries_of (Phant R)) :=
  let: tt := h in coef_series s i.

Local Notation "{ 'fps' R }" := (fpseries_of (Phant R)).
Local Notation coefs i := (coefps_head tt i).
Local Notation "s ``_ i" := (coef_series s i).

Lemma coefs_FPSeries (f : nat -> R) i : (FPSeries f)``_i = f i.
Proof. by rewrite unlock. Qed.

Definition fpsproj n (f : {fps R}) : {tfps R n} := [tfps i <= n => f``_i].

Lemma fpsprojP : iscompat fps_invsys fpsproj.
Proof.
rewrite /iscompat /= unlock /= => i j; rewrite leEnat => le_ij f /=.
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
Definition fpsind (_ : iscompat fps_invsys f) t : {fps R} :=
  FPSeries (fun i => (f i t)`_i).

Hypothesis Hcomp : iscompat fps_invsys f.
Lemma fpsindP i t : 'pi_i (fpsind Hcomp t) = f i t.
Proof.
rewrite /fpsind /=; apply tfpsP => j le_ji /=.
rewrite coef_tfps_of_fun le_ji coefs_FPSeries.
rewrite -leEnat in le_ji; rewrite -(Hcomp le_ji) /=.
by rewrite unlock coef_trXnt leqnn.
Qed.

Lemma fpsindE (un : T -> {fps R}) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 (fpsind Hcomp).
Proof.
move=> eqproj x; apply fpsprojE => i.
by rewrite -/(('pi_i \o un) _) eqproj fpsindP.
Qed.

End UniversalProperty.

(** Putting fps_bond below break inference for further canonical structures *)
Program Definition fps_invlim_Mixin :=
  @InvLimMixin _ _ _ _ (*fps_bond*) fps_invsys {fps R} fpsproj fpsind _ _ _.
Next Obligation. by move=> i j le_ij x; apply: fpsprojP. Qed.
Next Obligation. by move=> x /=; rewrite fpsindP. Qed.
Next Obligation. by move=> x; apply: (fpsindE Hcomp). Qed.
Canonical fps_invlimType :=
  Eval hnf in InvLimType {fps R} fps_invlim_Mixin.

Canonical fps_zmodType :=
  Eval hnf in ZmodType {fps R} [zmodMixin of {fps R} by <-].
Canonical fps_ringType :=
  Eval hnf in RingType {fps R} [ringMixin of {fps R} by <-].
Canonical fps_lmodType :=
  Eval hnf in LmodType R {fps R} [lmodMixin of {fps R} by <-].
Canonical fps_lalgType :=
  Eval hnf in LalgType R {fps R} [lalgMixin of {fps R} by <-].

End Defs.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with fpseries_of.
Bind Scope ring_scope with fpseries.

Arguments seriesfun {R} f%R.
Arguments seriesfun_inj {R} [s1%R s2%R] : rename.
Arguments coefps_head {R} h i%N s%R.
Arguments coef_series {R} s%R i%N.

Notation "{ 'fps' T }" := (fpseries_of (Phant T)).
Notation coefs i := (coefps_head tt i).
Notation "s ``_ i" := (coef_series s i).
Notation "\fps E .X^ i" := (FPSeries (fun i : nat => E) : {fps _}).


Section CoeffSeries.

Variable R : ringType.

Implicit Types (a b c: R) (s t u : {fps R}) (p q : {poly R}) (i j : nat).

Lemma coefs_piE i s : s``_i = ('pi_i s)`_i.
Proof. by rewrite coef_tfps_of_fun leqnn. Qed.

Lemma coefs_pi_leqE i j : (i <= j)%N -> forall s, s``_i = ('pi_j s)`_i.
Proof.
rewrite -leEnat => H s.
by rewrite coefs_piE -(ilprojE s H) /= fps_bondE coef_trXnt leqnn.
Qed.

Lemma coefsE i s : coefs i s = s``_i.
Proof. by []. Qed.

Lemma coefs0 i : (0 : {fps R })``_i = 0.
Proof. by rewrite coefs_piE raddf0 coef0. Qed.

Lemma coefs1 i : (1 : {fps R })``_i = (i == 0%N)%:R.
Proof. by rewrite coefs_piE rmorph1 coef1. Qed.

Lemma fpsP s t : (forall n, s``_n = t``_n) <-> (s = t).
Proof.
split => [Hco|-> //]; apply/fpsprojE => /= i; apply/tfpsP => j le_ji.
by rewrite -!(coefs_pi_leqE le_ji) Hco.
Qed.


Lemma coefs_is_additive i : additive (@coefps_head R tt i).
Proof. by move=> s t; rewrite !coefsE !coefs_piE !raddfB coefB. Qed.
Canonical coefs_additive i : {additive {fps R} -> R} :=
  Eval hnf in Additive (coefs_is_additive i).

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
Lemma coefs_sum I (r : seq I) (s : pred I) (F : I -> {fps R}) k :
  (\sum_(i <- r | s i) F i)``_k = \sum_(i <- r | s i) (F i)``_k.
Proof. exact: (raddf_sum (coefs_additive k)). Qed.


Lemma isthreadC c : isthread (fps_invsys R) (fun i => c%:S%tfps).
Proof. by move=> i j Hij; rewrite /= fps_bondE /= trXntC. Qed.
(* Definition seriesC c : {fps R} := InvLim (isthreadC c). *)
Definition fpsC c : {fps R} := ilthr (isthreadC c).
Local Notation "c %:S" := (fpsC c).

Lemma coefsC c i : c%:S``_i = (if i == 0%N then c else 0).
Proof. by rewrite coefs_piE invLimP coef_tfpsC. Qed.

Lemma fps0E : 0%:S = 0.
Proof. by apply/fpsP => i; rewrite coefs0 coefsC; case eqP. Qed.
Lemma fps1E : 1%:S = 1.
Proof. by apply/fpsP => i; rewrite coefs1 coefsC; case eqP. Qed.

Lemma fpsC_eq0 (c : R) : (c%:S == 0 :> {fps R}) = (c == 0).
Proof.
apply/eqP/eqP => [/(congr1 (coefs 0%N))|->]; last exact: fps0E.
by rewrite /= coefs0 coefsC.
Qed.

Lemma fpsCB : {morph fpsC : a b / a + b}.
Proof.
by move=> a b; apply/fpsP=>[[|i]]; rewrite coefsD !coefsC ?addr0. Qed.
Lemma fpsCN : {morph fpsC : c / - c}.
Proof. by move=> c; apply/fpsP=> [[|i]]; rewrite coefsN !coefsC ?oppr0. Qed.
Lemma fpsCD : {morph fpsC : a b / a - b}.
Proof. by move=> a b; rewrite fpsCB fpsCN. Qed.

Canonical fpsC_additive := Eval hnf in Additive fpsCD.

Lemma fpsCMn n : {morph fpsC : c / c *+ n}.
Proof. exact: raddfMn. Qed.
Lemma fpsCMNn n : {morph fpsC : c / c *- n}.
Proof. exact: raddfMNn. Qed.
Lemma fpsC_sum I (r : seq I) (s : pred I) (F : I -> R) :
  (\sum_(i <- r | s i) F i)%:S = \sum_(i <- r | s i) (F i)%:S.
Proof. exact: raddf_sum. Qed.


Lemma isthread_poly (p : {poly R}) :
  isthread (fps_invsys R) (fun n => trXn n p).
Proof. by move=> i j Hij; rewrite /= fps_bondE /trXnt /= trXn_trXn. Qed.
Definition fps_poly (p : {poly R}) : {fps R} := ilthr (isthread_poly p).

Lemma coefs_fps_poly p i : (fps_poly p)``_i = p`_i.
Proof. by rewrite coefs_piE invLimP coef_trXn leqnn. Qed.

Lemma fps_polyK n p :
  (n >= size p)%N -> tfps ('pi_n (fps_poly p)) = p.
Proof.
move=> Hn; apply/polyP => i; case: (leqP i n) => [le_in|lt_ni].
- by rewrite -[LHS](coefs_pi_leqE le_in) coefs_fps_poly.
- by rewrite coef_tfps leqNgt lt_ni [RHS]nth_default ?(leq_trans Hn (ltnW _)).
Qed.

Lemma fps_poly_inj : injective fps_poly.
Proof.
move=> p q /(congr1 ('pi_(maxn (size p) (size q))))/(congr1 tfps).
by rewrite !fps_polyK ?leq_maxr ?leq_maxl.
Qed.


Fact fps_poly_is_additive : additive fps_poly.
Proof.
move=> p q; apply/fpsP => n.
by rewrite coefsB !coefs_piE !invLimP raddfB /= coeftB /=.
Qed.
Canonical fps_poly_additive :=
  Eval hnf in Additive fps_poly_is_additive.

Lemma fps_polyD p q : fps_poly (p + q) = fps_poly p + fps_poly q.
Proof. exact: raddfD. Qed.
Lemma fps_polyN p : fps_poly (- p) = - fps_poly p.
Proof. exact: raddfN. Qed.
Lemma fps_polyB p q : fps_poly (p - q) = fps_poly p - fps_poly q.
Proof. exact: raddfB. Qed.
Lemma fps_polyMn p n : fps_poly (p *+ n) = (fps_poly p) *+ n.
Proof. exact: raddfMn. Qed.
Lemma fps_polyMNn p n : fps_poly (p *- n) = (fps_poly p) *- n.
Proof. exact: raddfMNn. Qed.
Lemma fps_poly_sum I (r : seq I) (s : pred I) (F : I -> {poly R}) :
  fps_poly (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) fps_poly (F i).
Proof. exact: raddf_sum. Qed.


Lemma poly_fps_eqP s t :
  (forall n, 'pi_n s = 'pi_n t) <-> (s = t).
Proof. by split => [|-> //]; apply: invlimE. Qed.

Lemma poly_fpsC n c : tfps ('pi_n c%:S) = c%:P :> {poly R}.
Proof. by apply/polyP => i; rewrite invLimP coef_tfpsC coefC. Qed.

Lemma fps_polyC c : fps_poly c%:P = c%:S.
Proof. by apply/fpsP => n; rewrite coefs_fps_poly coefC coefsC. Qed.


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

Fact coefs0_multiplicative : multiplicative (coefs 0 : {fps R} -> R).
Proof.
split=> [s t|] /=; last by rewrite coefs1.
by rewrite coefsM big_ord_recl big_ord0 addr0 /= subnn.
Qed.
Canonical coefs0_rmorphism := Eval hnf in AddRMorphism coefs0_multiplicative.


Fact fps_poly_is_rmorphism : rmorphism fps_poly.
Proof.
split; first exact: fps_poly_is_additive.
split=> [p q|]; apply/fpsP=> i; first last.
  by rewrite !coefs_piE !invLimP /= trXn1.
rewrite coefs_fps_poly coefM coefsM; apply: eq_bigr => j _.
by rewrite !coefs_fps_poly.
Qed.
Canonical fps_poly_rmorphism :=
  Eval hnf in RMorphism fps_poly_is_rmorphism.

Lemma fps_polyX n : {morph fps_poly : p / p ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma fps_poly1 : fps_poly 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma fps_polyM : {morph fps_poly : x y  / x * y}.
Proof. exact: rmorphM. Qed.

Lemma mul_fpsC a s : a%:S * s = a *: s.
Proof.
apply/poly_fps_eqP => i.
by rewrite linearZ /= !invLimP -alg_tfpsC mulr_algl.
Qed.

Lemma coefsZ a s i : (a *: s)``_i = a * s``_i.
Proof. by rewrite !coefs_piE linearZ coefZ. Qed.

Lemma alg_fpsC a : a%:A = a%:S :> {fps R}.
Proof. by rewrite -mul_fpsC mulr1. Qed.

Canonical coefps_linear i : {scalar {fps R}} :=
  Eval hnf in AddLinear
                ((fun a => (coefsZ a) ^~ i) : scalable_for *%R (coefs i)).
Canonical coefp0_lrmorphism :=
  Eval hnf in [lrmorphism of coefs 0].


Fact fps_poly_is_scalable : scalable fps_poly.
Proof.
move=> c p; apply/fpsP => n.
by rewrite coefsZ !coefs_fps_poly coefZ.
Qed.
Canonical fps_poly_linear :=
  Eval hnf in AddLinear fps_poly_is_scalable.
Canonical fps_poly_lrmorphism :=
  Eval hnf in [lrmorphism of fps_poly].


Local Notation "''X" := (locked (@fps_poly 'X)).
Local Notation "'''X^' n" := (''X ^+ n).

Lemma proj_fpsX n : 'pi_n ''X = (\X)%tfps.
Proof. by rewrite -lock invLimP. Qed.
Lemma proj_fpsXn n i : 'pi_n ''X^i = (\X)%tfps^+i.
Proof. by rewrite !rmorphX /= proj_fpsX. Qed.
Lemma coef_fpsX i : (''X ``_i) = (i == 1%N)%:R :> R.
Proof. by rewrite -lock coefs_fps_poly coefX. Qed.
Lemma coef_fpsXn n i : (''X^n ``_i) = (i == n)%:R :> R.
Proof. by rewrite -lock -rmorphX /= coefs_fps_poly coefXn. Qed.

Lemma fpsX_eq0 : (''X == 0 :> {fps R}) = false.
Proof.
apply/negP => /eqP/fpsP/(_ 1%N)/eqP.
by rewrite coef_fpsX coefs0 /= oner_eq0.
Qed.

Lemma commr_fpsX s : GRing.comm s ''X.
Proof.
apply/fpsP=> i; rewrite coefsMr coefsM.
by apply: eq_bigr => j _; rewrite coef_fpsX commr_nat.
Qed.

Lemma commr_fpsXn n s : GRing.comm s ''X^n.
Proof. exact/commrX/commr_fpsX. Qed.

Lemma coef_fpsXM f i :
  (''X * f)``_i = if i == 0%N then 0 else f``_i.-1.
Proof.
rewrite !coefs_piE rmorphM /= proj_fpsX coef_tfpsXM leqnn.
by rewrite -coefs_piE -coefs_pi_leqE // leq_pred.
Qed.

Lemma coef_fpsXnM f k i :
  (''X^k * f)``_i = if (i < k)%N then 0 else f``_(i - k).
Proof.
rewrite !coefs_piE rmorphM rmorphX /= proj_fpsX coef_tfpsXnM leqnn.
by rewrite -coefs_piE -coefs_pi_leqE // leq_subr.
Qed.

Lemma expr_cX (c : R) i : (c *: ''X) ^+ i = (c ^+ i) *: ''X^i.
Proof.
apply invlimE => j.
by rewrite !(rmorphX, linearZ) /= proj_fpsX expr_cX.
Qed.

End CoeffSeries.

Coercion fps_poly : poly_of >-> fpseries_of.

Arguments fpsC {R}.
Arguments fps_poly {R}.
Notation "c %:S" := (fpsC c).
Notation "''X" := (locked (@fps_poly _ 'X)).
Notation "'''X^' n" := (''X ^+ n).


Section FpsUnitRing.

Variable R : unitRingType.
Implicit Type f : {fps R}.

Canonical fps_unitRingType :=
  Eval hnf in UnitRingType {fps R} [unitRingMixin of {fps R} by <-].

Lemma unit_fpsE f : (f \is a GRing.unit) = (f``_0 \is a GRing.unit).
Proof.
apply/ilunitP/idP => [/(_ 0%N) | Hu i]; first by rewrite coefs_piE -unit_tfpsE.
by rewrite unit_tfpsE -coefs_pi_leqE.
Qed.

Lemma coef0_fpsV f : (f^-1)``_0 = (f``_0)^-1.
Proof.
rewrite !coefs_piE -coef0_tfpsV.
case (boolP (f \is a GRing.unit)) => [/rmorphV -> // | ninv].
by rewrite !invr_out // unit_tfpsE -coefs_piE -unit_fpsE.
Qed.

Lemma coef_fpsV f i :
  f \is a GRing.unit ->
  f^-1``_i = if i == 0%N then f``_0 ^-1
             else - (f``_0 ^-1) * (\sum_(j < i) f``_j.+1 * f^-1``_(i - j.+1)).
Proof.
move=> funit.
rewrite coefs_piE (rmorphV _ funit) //=.
rewrite [LHS](coef_tfpsV _ (rmorph_unit _ funit)) // ltnn.
case: eqP => [->| _]; first by rewrite -coefs_piE.
rewrite -coefs_pi_leqE //; congr (_ * _); apply eq_bigr => [] [j ltji] _.
rewrite -!coefs_pi_leqE //=; congr (_ * _).
by rewrite -(rmorphV _ funit) //= -!coefs_pi_leqE // leq_subr.
Qed.

End FpsUnitRing.


Section FpsComRing.

Variable R : comRingType.

Canonical fps_comRingType :=
  Eval hnf in ComRingType {fps R} [comRingMixin of {fps R} by <-].
Canonical fps_algType :=
  Eval hnf in AlgType R {fps R} [algMixin of {fps R} by <-].

Lemma test1 i : 'pi_i (1 : {fps R}) = 1.
Proof. exact: rmorph1. Qed.

Lemma test2 i c (x : {fps R}) : 'pi_i (c *: x) = c *: ('pi_i x).
Proof. by rewrite linearZ. Qed.

End FpsComRing.


Section FpsComUnitRing.

Variable R : comUnitRingType.

Canonical fps_comUnitRingType :=
  Eval hnf in [comUnitRingType of {fps R}].
Canonical fps_unitalgType :=
  Eval hnf in [unitAlgType R of {fps R}].
(* Canonical fps_comUnitAlgType :=
  Eval hnf in [comUnitAlgType of {fps R}]. *)

End FpsComUnitRing.


Section Valuation.

Variable R : ringType.
Implicit Type s : {fps R}.

(** Valuation of a fps *)
Definition valuat s : natbar :=
  if pselect (exists n, s``_n != 0) is left Pf
  then Nat (ex_minn Pf) else Inf.
Definition slead s : R :=
  if valuat s is Nat n then s``_n else 0.

Variant valuat_spec s : natbar -> Set :=
  | ValNat n of s``_n != 0 & (forall i, (i < n)%N -> s``_i = 0) :
      valuat_spec s (Nat n)
  | ValInf of s = 0 : valuat_spec s Inf.

Lemma valuatP s : valuat_spec s (valuat s).
Proof.
rewrite /valuat; case: pselect => [Pf|NPf].
- case: ex_minnP => v Hv vmin; apply ValNat => [|i iv]; first exact: Hv.
  by apply/contraTeq : iv; rewrite -leqNgt; exact: vmin.
- apply ValInf; apply fpsP => n; rewrite coefs0.
  apply/eqP; rewrite -(negbK (_ == 0)); apply/negP => Hn.
  by apply NPf; exists n.
Qed.

Lemma coefs_le_valuat s n : (Nat n < valuat s)%O -> s``_n = 0.
Proof.
case: valuatP => [v Hv vmin /= |->]; last by rewrite coefs0.
by rewrite ltEnatbar; apply: vmin.
Qed.

Lemma valuatNatE s n :
  s``_n != 0 -> (forall i, (i < n)%N -> s``_i = 0) -> valuat s = Nat n.
Proof.
case: valuatP => [v Hv vmin /= |->]; last by rewrite coefs0 eqxx.
move=> Hn /(_ v)/contra_neqN/(_ Hv); rewrite -leqNgt => nlev.
congr Nat; apply anti_leq; rewrite {}nlev andbT.
by move: vmin => /(_ n)/contra_neqN/(_ Hn); rewrite -leqNgt.
Qed.

Variant valuatXn_spec s : natbar -> Type :=
  | ValXnNat n t of t``_0 != 0 & s = ''X^n * t : valuatXn_spec s (Nat n)
  | ValXnInf of s = 0 : valuatXn_spec s Inf.

Lemma valuatXnP s : valuatXn_spec s (valuat s).
Proof.
case: valuatP => [v Hv vmin /= |-> //].
- apply: (ValXnNat (t := \fps s``_(v + i) .X^i)).
  + by rewrite coefs_FPSeries addn0.
  + apply/fpsP => n; rewrite coef_fpsXnM; case: ltnP; first exact: vmin.
    by rewrite coefs_FPSeries => /subnKC ->.
- by apply ValXnInf; apply fpsP => n; rewrite coefs0.
Qed.

Lemma valuatXnE s n : s``_0 != 0 -> valuat (''X ^+ n * s) = Nat n.
Proof.
move=> Hs.
by apply valuatNatE => [|i Hi]; rewrite coef_fpsXnM ?ltnn ?subnn // Hi.
Qed.

Lemma valuatXn_leP s n :
  reflect (exists t, s = (''X ^+ n) * t) (Nat n <= valuat s)%O.
Proof.
case: valuatXnP => [v t Ht|]->{s}; apply (iffP idP) => //=.
- rewrite leEnatbar => nlev.
  exists (''X ^+ (v - n) * t); rewrite mulrA.
  by rewrite -exprD subnKC //.
- rewrite leEnatbar => [] [s] /(congr1 (coefs v)) /=.
  by apply contra_eqT; rewrite -ltnNge !coef_fpsXnM /= ltnn subnn => ->.
- by move=> _; exists 0; rewrite mulr0.
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite coefs0 eq_refl. Qed.
Lemma slead0 : slead 0 = 0.
Proof. by rewrite /slead valuat0. Qed.

Lemma valuat_fpsC c : valuat c%:S = if c == 0 then Inf else Nat 0.
Proof.
case: (altP (c =P 0)) => [->|Hc]/=; first by rewrite fps0E valuat0.
by apply valuatNatE; rewrite // coefsC.
Qed.
Lemma slead_coefsC c : slead c%:S = c.
Proof.
by rewrite /slead valuat_fpsC; case: eqP => [->|_]; rewrite ?coefsC.
Qed.

Lemma valuat1 : valuat 1 = Nat 0.
Proof. by rewrite -fps1E valuat_fpsC oner_eq0. Qed.
Lemma slead1 : slead 1 = 1.
Proof. by rewrite /slead valuat1 coefs1. Qed.

Lemma valuatInfE s : (s == 0 :> {fps R}) = (valuat s == Inf).
Proof.
apply/eqP/eqP => [-> |]; first exact: valuat0.
by case: valuatP.
Qed.
Lemma slead0E s : (s == 0 :> {fps R}) = (slead s == 0).
Proof.
rewrite /slead; case: valuatP => [n Hn _|->]; last by rewrite !eqxx.
rewrite (negbTE Hn); apply/contraNF: Hn => /eqP ->.
by rewrite coefs0.
Qed.


Lemma valuatN s : valuat (- s) = valuat s.
Proof.
case: (valuatXnP s) => [v t Ht|]->{s}; last by rewrite oppr0 valuat0.
by rewrite -mulrN valuatXnE // coefsN oppr_eq0.
Qed.
Lemma sleadN s : slead (- s) = - slead s.
Proof.
rewrite /slead valuatN; case: (valuat s); rewrite ?oppr0 // => n.
by rewrite coefsN.
Qed.

Lemma valuatXnM s n : valuat (''X ^+ n * s) = addbar (Nat n) (valuat s).
Proof.
case: (valuatXnP s) => [v t Ht|]->{s}; last by rewrite mulr0 valuat0.
by rewrite /= mulrA -exprD valuatXnE.
Qed.
Lemma sleadXnM s n : slead (''X ^+ n * s) = slead s.
Proof.
rewrite /slead valuatXnM; case: (valuat s) => //= v.
by rewrite coef_fpsXnM ltnNge leq_addr /= addKn.
Qed.

Lemma valuatXM s : valuat (''X * s) = addbar (Nat 1) (valuat s).
Proof. by rewrite -valuatXnM expr1. Qed.
Lemma sleadXM s : slead (''X * s) = slead s.
Proof.
rewrite /slead valuatXM; case: (valuat s) => //= v.
by rewrite coef_fpsXM add1n.
Qed.

Lemma valuatXn n : valuat (''X ^+ n) = Nat n.
Proof. by rewrite -(mulr1 (''X ^+ n)) valuatXnM valuat1 /= addn0. Qed.
Lemma sleadXn n : slead (''X ^+ n) = 1.
Proof. by rewrite /slead valuatXn coef_fpsXn eqxx. Qed.

Lemma valuatX : valuat ''X = Nat 1.
Proof. by rewrite -valuatXn expr1. Qed.
Lemma sleadX : slead ''X = 1.
Proof. by rewrite /slead valuatX coef_fpsX eqxx. Qed.

Lemma valuatD s1 s2 :
  (valuat s1 `&` valuat s2 <= valuat (s1 + s2))%O.
Proof.
wlog v1lev2 : s1 s2 / (valuat s1 <= valuat s2)%O.
  move=> Hlog; case: (leP (valuat s1) (valuat s2)) => [|/ltW]/Hlog//.
  by rewrite addrC meetC.
rewrite (meet_idPl v1lev2); move: v1lev2.
case: (valuatXnP s1) => [v t1 Ht1|]->{s1}.
- move/valuatXn_leP=> [t2]->{s2}; apply/valuatXn_leP.
  by exists (t1 + t2); rewrite mulrDr.
- by rewrite le1x -valuatInfE => /eqP ->; rewrite addr0 valuat0.
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
apply valuatNatE=> [|n nv1]; rewrite coefsD v2min ?addr0 // ?v1min //.
exact: ltn_trans nv1 v12.
Qed.
Lemma sleadDr s1 s2 :
  (valuat s1 < valuat s2)%O -> slead (s1 + s2) = slead s1.
Proof.
rewrite /slead => H; rewrite (valuatDr H).
move: H; case: (valuat s1) => // v.
case: (valuatP s2) => [v2 _ v2min | -> _]; last by rewrite addr0.
by rewrite coefsD ltEnatbar => /v2min ->; rewrite addr0.
Qed.

Lemma valuatBr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 - s2) = valuat s1.
Proof. by rewrite -(valuatN s2) => /valuatDr. Qed.
Lemma sleadBr s1 s2 :
  (valuat s1 < valuat s2)%O -> slead (s1 - s2) = slead s1.
Proof. by rewrite -(valuatN s2); apply sleadDr. Qed.

Lemma valuatBl s1 s2 :
  (valuat s2 < valuat s1)%O -> valuat (s1 - s2) = valuat s2.
Proof. by rewrite -(valuatN s2) addrC => /valuatDr. Qed.
Lemma sleadBl s1 s2 :
  (valuat s2 < valuat s1)%O -> slead (s1 - s2) = - slead s2.
Proof. by move/sleadBr => <-; rewrite -sleadN opprD addrC opprK. Qed.

Lemma valuatMge s1 s2 :
  (addbar (valuat s1) (valuat s2) <= valuat (s1 * s2))%O.
Proof.
case: (valuatXnP s1) => [v1 t1 Ht1|]->{s1}; last by rewrite mul0r valuat0.
case: (valuatXnP s2) => [v2 t2 Ht2|]->{s2}; last by rewrite mulr0 valuat0.
rewrite /= mulrA (commr_fpsXn v2) mulrA -exprD addnC.
by apply/valuatXn_leP; exists (t1 * t2); rewrite mulrA.
Qed.
End Valuation.
Arguments valuat0 {R}.
Arguments valuat1 {R}.
Arguments slead  {R}.
Arguments slead0 {R}.
Arguments slead1 {R}.


Section FPSIDomain.

Variable R : idomainType.

Implicit Types (a b c : R) (s t : {fps R}).

Lemma valuatM s1 s2 :
  valuat (s1 * s2) = addbar (valuat s1) (valuat s2).
Proof.
case: (valuatXnP s1)=> [v1 t1 Hv1|]->{s1} /=; last by rewrite !mul0r valuat0.
case: (valuatXnP s2)=> [v2 t2 Hv2|]->{s2} /=; last by rewrite !mulr0 valuat0.
rewrite mulrA (commr_fpsXn v2) mulrA -exprD addnC -mulrA.
apply: valuatXnE; rewrite coefsM big_ord_recr big_ord0 /= add0r subn0.
by rewrite mulf_eq0 negb_or Hv1 Hv2.
Qed.

Lemma valuat_prod (I : Type ) (s : seq I) (P : pred I) (F : I -> {fps R}) :
  valuat (\prod_(i <- s | P i) F i) =
  \big[addbar/Nat 0]_(i <- s | P i) valuat (F i).
Proof. exact: (big_morph _ valuatM valuat1). Qed.

Lemma sleadM : {morph (@slead R) : s1 s2 / s1 * s2}.
Proof.
move=> s1 s2; rewrite /slead valuatM.
case: (valuatXnP s1)=> [v1 t1 Hv1|]->{s1} /=; last by rewrite !mul0r.
case: (valuatXnP s2)=> [v2 t2 Hv2->{s2}| _]; last by rewrite !mulr0.
rewrite mulrA (commr_fpsXn v2) mulrA -exprD addnC -mulrA.
by rewrite !coef_fpsXnM !ltnn !subnn coefsM big_ord_recr big_ord0 /= add0r subn0.
Qed.
Lemma slead_prod (I : Type ) (s : seq I) (P : pred I) (F : I -> {fps R}) :
  slead (\prod_(i <- s | P i) F i) = \prod_(i <- s | P i) slead (F i).
Proof. exact: (big_morph _ sleadM slead1). Qed.

Fact series_idomainAxiom s t :
  s * t = 0 -> (s == 0 :> {fps R}) || (t == 0 :> {fps R}).
Proof. by move/eqP; rewrite !valuatInfE valuatM addbar_eqI. Qed.

Canonical series_idomainType :=
  Eval hnf in IdomainType {fps R} series_idomainAxiom.

End FPSIDomain.
Arguments valuatM {R}.
Arguments sleadM {R}.


