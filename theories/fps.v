(** Formal power series *)
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
From mathcomp Require Import order.

Require Import auxresults natbar directed tfps invlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Import GRing.Theory.
Local Open Scope ring_scope.

Declare Scope fps_scope.
Delimit Scope fps_scope with fps.

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
Reserved Notation "f \oS g" (at level 50).


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
by apply trXnt_is_multiplicative; rewrite -leEnat.
Qed.
Canonical bond_additive  := Eval hnf in Additive bond_is_rmorphism.
Canonical bond_rmorphism := Eval hnf in RMorphism bond_is_rmorphism.

Lemma bond_is_linear : linear (fps_bond le_ij).
Proof. by rewrite unlock; exact: trXnt_is_linear. Qed.
Canonical bond_linear     := Eval hnf in AddLinear bond_is_linear.
Canonical bond_lrmorphism := Eval hnf in [lrmorphism of (fps_bond le_ij)].

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

Lemma fpsprojP : cone fps_invsys fpsproj.
Proof.
rewrite /cone /= unlock /= => i j; rewrite leEnat => le_ij f /=.
apply tfpsP=> k le_ki.
by rewrite coef_trXnt le_ki !coef_tfps_of_fun le_ki (leq_trans le_ki le_ij).
Qed.

Local Notation "''pi_' i" := (fpsproj i).

Lemma fpsprojE x y : (forall i : nat, 'pi_i x = 'pi_i y) -> x = y.
Proof.
rewrite /fpsproj => eqxy; apply/seriesfun_inj/funext => i.
have:= congr1 (fun t : {tfps R i} => t`_i) (eqxy i).
by rewrite !coef_tfps_of_fun leqnn unlock.
Qed.

(** Building the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, T -> {tfps R i}).
Definition fpsind of cone fps_invsys f := fun t =>
  FPSeries (fun i => (f i t)`_i).

Hypothesis Hcone : cone fps_invsys f.
Lemma fpsindP i t : 'pi_i (fpsind Hcone t) = f i t.
Proof.
rewrite /fpsind /=; apply tfpsP => j le_ji /=.
rewrite coef_tfps_of_fun le_ji coefs_FPSeries.
rewrite -leEnat in le_ji; rewrite -(Hcone le_ji) /=.
by rewrite unlock coef_trXnt leqnn.
Qed.

Lemma fpsindE (un : T -> {fps R}) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 (fpsind Hcone).
Proof.
move=> eqproj x; apply fpsprojE => i.
by rewrite -/(('pi_i \o un) _) eqproj fpsindP.
Qed.

End UniversalProperty.

(** Putting fps_bond below break inference for further canonical structures *)
Program Definition fps_invlimMixin :=
  @InvLimMixin _ _ _ _ (*fps_bond*) fps_invsys {fps R} fpsproj fpsind _ _ _.
Next Obligation. by move=> i j le_ij x; apply: fpsprojP. Qed.
Next Obligation. by move=> x /=; rewrite fpsindP. Qed.
Next Obligation. by move=> x; apply: (fpsindE Hcone). Qed.
Canonical fps_invlimType :=
  Eval hnf in InvLimType {fps R} fps_invlimMixin.

Canonical fps_zmodType :=
  Eval hnf in ZmodType {fps R} [zmodMixin of {fps R} by <-].
Canonical fps_zmodInvLimType :=
  Eval hnf in ZmodInvLimType {fps R} [zmodInvLimMixin of {fps R} by <-].
Canonical fps_ringType :=
  Eval hnf in RingType {fps R} [ringMixin of {fps R} by <-].
Canonical fps_ringInvLimType :=
  Eval hnf in RingInvLimType {fps R} [ringInvLimMixin of {fps R} by <-].
Canonical fps_lmodType :=
  Eval hnf in LmodType R {fps R} [lmodMixin of {fps R} by <-].
Canonical fps_lmodInvLimType :=
  Eval hnf in LmodInvLimType R {fps R} [lmodInvLimMixin of {fps R} by <-].
Canonical fps_lalgType :=
  Eval hnf in LalgType R {fps R} [lalgMixin of {fps R} by <-].
Canonical fps_lalgInvLimType :=
  Eval hnf in LalgInvLimType R {fps R}.

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
Notation "\fps E .X^ i" := (FPSeries (fun i : nat => E)).


Section CoeffSeries.

Variable R : ringType.

Implicit Types (a b c: R) (s t u : {fps R}) (p q : {poly R}) (i j : nat).

Lemma proj0 i : 'pi[{fps R}]_i 0 = 0.
Proof. exact: raddf0. Qed.
Lemma projD i s t : 'pi_i (s + t) = 'pi_i s + 'pi_i t.
Proof. exact: raddfD. Qed.
Lemma projN i s : 'pi_i (- s) = - ('pi_i s).
Proof. exact: raddfN. Qed.
Lemma projB i s t : 'pi_i (s - t) = 'pi_i s - 'pi_i t.
Proof. exact: raddfB. Qed.
Lemma projMn i s n : 'pi_i (s *+ n) = ('pi_i s) *+ n.
Proof. exact: raddfMn. Qed.
Lemma projMNn i s n : 'pi_i (s *- n) = ('pi_i s) *- n.
Proof. exact: raddfMNn. Qed.
Lemma proj_sum k I (r : seq I) (s : pred I) (F : I -> {fps R}) :
  'pi_k (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) 'pi_k (F i).
Proof. exact: raddf_sum. Qed.

Lemma proj1 i : 'pi[{fps R}]_i 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma projM i : {morph 'pi[{fps R}]_i : x y  / x * y}.
Proof. exact: rmorphM. Qed.
Lemma projX i n : {morph 'pi[{fps R}]_i : p / p ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma proj_prod k I (r : seq I) (s : pred I) (F : I -> {fps R}) :
  'pi_k (\prod_(i <- r | s i) F i) = \prod_(i <- r | s i) 'pi_k (F i).
Proof. exact: rmorph_prod. Qed.

Lemma projZ i c : {morph 'pi[{fps R}]_i : x / c *: x}.
Proof. exact: linearZ. Qed.

Local Definition proj_simp :=
  (proj0, projD, projN, projB, projMn, projMNn, proj_sum,
   proj1, projM, projX, proj_prod, projZ).

Lemma coefs_projE i s : s``_i = ('pi_i s)`_i.
Proof. by rewrite coef_tfps_of_fun leqnn. Qed.

Lemma coeft_proj i j : (i <= j)%N -> forall s, ('pi_j s)`_i = s``_i.
Proof.
rewrite -leEnat => H s.
by rewrite coefs_projE -(ilprojE s H) /= fps_bondE coef_trXnt leqnn.
Qed.

Lemma coefsE i s : coefs i s = s``_i.
Proof. by []. Qed.

Lemma coefs0 i : (0 : {fps R })``_i = 0.
Proof. by rewrite coefs_projE proj_simp coef0. Qed.

Lemma coefs1 i : (1 : {fps R })``_i = (i == 0%N)%:R.
Proof. by rewrite coefs_projE proj_simp coef1. Qed.

Lemma fpsP s t : (forall n, s``_n = t``_n) <-> (s = t).
Proof.
split => [Hco|-> //]; apply/fpsprojE => /= i; apply/tfpsP => j le_ji.
by rewrite !(coeft_proj le_ji) Hco.
Qed.


Lemma coefs_is_additive i : additive (@coefps_head R tt i).
Proof. by move=> s t; rewrite !coefsE !coefs_projE projB coefB. Qed.
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


Fact compat_fpsC : cone (fps_invsys R) (@tfpsC R).
Proof. by move=> i j le_ij c /=; rewrite fps_bondE trXntC. Qed.
Definition fpsC : R^o -> {fps R} := 'ind compat_fpsC.
Local Notation "c %:S" := (fpsC c).

Lemma proj_fpsC i c : 'pi_i c%:S = c%:S%tfps.
Proof. exact: piindE. Qed.

Lemma coefsC c i : c%:S``_i = (if i == 0%N then c else 0).
Proof. by rewrite coefs_projE piindE coeftC. Qed.

Fact fpsC_is_additive : additive fpsC.
Proof. exact: (raddfB (ilind_additive _ compat_fpsC)). Qed.
Canonical fpsC_additive := Eval hnf in Additive fpsC_is_additive.
Fact fpsC_is_multiplicative : multiplicative fpsC.
Proof. exact: ilind_is_multiplicative _ compat_fpsC. Qed.
Canonical fpsC_rmorphism := AddRMorphism fpsC_is_multiplicative.

Lemma fpsCK : cancel fpsC (coefs 0%N).
Proof. by move=> c; rewrite /= coefsC. Qed.
Lemma fpsC_inj : injective fpsC.
Proof. exact: can_inj fpsCK. Qed.

Lemma fpsC0 : 0%:S = 0.
Proof. exact: rmorph0. Qed.
Lemma fpsCB : {morph fpsC : a b / a + b}.
Proof. exact: rmorphD. Qed.
Lemma fpsCN : {morph fpsC : c / - c}.
Proof. exact: rmorphN. Qed.
Lemma fpsCD : {morph fpsC : a b / a - b}.
Proof. exact: rmorphB. Qed.
Lemma fpsCMn n : {morph fpsC : c / c *+ n}.
Proof. exact: rmorphMn. Qed.
Lemma fpsCMNn n : {morph fpsC : c / c *- n}.
Proof. exact: rmorphMNn. Qed.
Lemma fpsC_sum I (r : seq I) (s : pred I) (F : I -> R) :
  (\sum_(i <- r | s i) F i)%:S = \sum_(i <- r | s i) (F i)%:S.
Proof. exact: rmorph_sum. Qed.

Lemma fpsC1 : 1%:S = 1.
Proof. exact: rmorph1. Qed.
Lemma fpsCM : {morph fpsC : a b / a * b}.
Proof. exact: rmorphM. Qed.
Lemma fpsCX n : {morph fpsC : c / c ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma fpsC_prod I (r : seq I) (s : pred I) (F : I -> R) :
  (\prod_(i <- r | s i) F i)%:S = \prod_(i <- r | s i) (F i)%:S.
Proof. exact: rmorph_prod. Qed.

Lemma fpsC_eq0 (c : R) : (c%:S == 0 :> {fps R}) = (c == 0).
Proof. rewrite -fpsC0; apply/inj_eq/fpsC_inj. Qed.
Lemma fpsC_eq1 (c : R) : (c%:S == 1 :> {fps R}) = (c == 1).
Proof. rewrite -fpsC1; apply/inj_eq/fpsC_inj. Qed.

Lemma compat_poly : cone (fps_invsys R) (@trXn R).
Proof. by  move=> i j le_ij p; rewrite /= fps_bondE /trXnt /= trXn_trXn. Qed.
Definition fps_poly : {poly R} -> {fps R} := 'ind compat_poly.

Lemma proj_fps_poly i p : 'pi_i (fps_poly p) = trXn i p.
Proof. exact: piindE. Qed.

Lemma coefs_fps_poly i p : (fps_poly p)``_i = p`_i.
Proof. by rewrite coefs_projE piindE coef_trXn leqnn. Qed.

Lemma fps_polyK n p :
  (size p <= n.+1)%N -> tfps ('pi_n (fps_poly p)) = p.
Proof. by rewrite proj_fps_poly; apply: trXnK. Qed.

Lemma fps_poly_inj : injective fps_poly.
Proof.
move=> p q /(congr1 ('pi_(maxn (size p) (size q))))/(congr1 tfps).
by rewrite !fps_polyK // (leq_trans _ (leqnSn _)) // ?leq_maxr ?leq_maxl.
Qed.

Fact fps_poly_is_linear : linear fps_poly.
Proof. exact: (linearP (ilind_linear _ compat_poly)). Qed.
Canonical fps_poly_additive := Eval hnf in Additive fps_poly_is_linear.
Canonical fps_poly_linear := Eval hnf in Linear fps_poly_is_linear.
Fact fps_poly_is_multiplicative : multiplicative fps_poly.
Proof. exact: ilind_is_multiplicative _ compat_poly. Qed.
Canonical fps_poly_rmorphism :=
  Eval hnf in AddRMorphism fps_poly_is_multiplicative.
Canonical fps_poly_lrmorphism := [lrmorphism of fps_poly].

Lemma fps_poly0 : fps_poly 0 = 0.
Proof. exact: raddf0. Qed.
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

Lemma fps_polyX n : {morph fps_poly : p / p ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma fps_poly1 : fps_poly 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma fps_polyM : {morph fps_poly : x y  / x * y}.
Proof. exact: rmorphM. Qed.
Lemma fps_poly_prod I (r : seq I) (s : pred I) (F : I -> {poly R}) :
  fps_poly (\prod_(i <- r | s i) F i) = \prod_(i <- r | s i) fps_poly (F i).
Proof. exact: rmorph_prod. Qed.


Lemma poly_fps_eqP s t :
  (forall n, 'pi_n s = 'pi_n t) <-> (s = t).
Proof. by split => [|-> //]; apply: invlimE. Qed.

Lemma poly_fpsC n c : tfps ('pi_n c%:S) = c%:P :> {poly R}.
Proof. by apply/polyP => i; rewrite piindE coeftC coefC. Qed.

Lemma fps_polyC c : fps_poly c%:P = c%:S.
Proof. by apply/fpsP => n; rewrite coefs_fps_poly coefC coefsC. Qed.


Fact coefsM s t i : (s * t)``_i = \sum_(j < i.+1) s``_j * t``_(i - j).
Proof.
rewrite coefs_projE ilthrP /= coeftM leqnn.
apply eq_bigr => [[j]] /=; rewrite ltnS => le_ji _.
by rewrite !coeft_proj ?leq_subr.
Qed.
Lemma coefsMr s t n : (s * t)``_n = \sum_(j < n.+1) s``_(n - j) * t``_j.
Proof.
rewrite coefs_projE ilthrP /= coeftMr leqnn.
apply eq_bigr => [[j]] /=; rewrite ltnS => le_ji _.
by rewrite ?coeft_proj ?leq_subr.
Qed.

Fact coefs0_multiplicative : multiplicative (coefs 0 : {fps R} -> R).
Proof.
split=> [s t|] /=; last by rewrite coefs1.
by rewrite coefsM big_ord_recl big_ord0 addr0 /= subnn.
Qed.
Canonical coefs0_rmorphism := Eval hnf in AddRMorphism coefs0_multiplicative.

Lemma coefs0M s t : (s * t)``_0 = s``_0 * t``_0.
Proof. exact: (rmorphM coefs0_rmorphism). Qed.
Lemma coefs0X s i : (s ^+ i)``_0 = s``_0 ^+ i.
Proof. exact: (rmorphX coefs0_rmorphism). Qed.
Lemma coef0_prod I (r : seq I) (s : pred I) (F : I -> {fps R}) :
  (\prod_(i <- r | s i) F i)``_0 = \prod_(i <- r | s i) (F i)``_0.
Proof. exact: (rmorph_prod coefs0_rmorphism). Qed.

Lemma mul_fpsC a s : a%:S * s = a *: s.
Proof.
apply/poly_fps_eqP => i.
by rewrite linearZ /= rmorphM /= proj_fpsC -alg_tfpsC mulr_algl.
Qed.

Lemma coefsZ a s i : (a *: s)``_i = a * s``_i.
Proof. by rewrite !coefs_projE linearZ coefZ. Qed.

Lemma alg_fpsC a : a%:A = a%:S :> {fps R}.
Proof. by rewrite -mul_fpsC mulr1. Qed.

Canonical coefps_linear i : {scalar {fps R}} :=
  Eval hnf in AddLinear
                ((fun a => (coefsZ a) ^~ i) : scalable_for *%R (coefs i)).
Canonical coefp0_lrmorphism :=
  Eval hnf in [lrmorphism of coefs 0].

Lemma proj0CE f : 'pi[{fps R}]_0%N f = (f``_0%N)%:S%tfps.
Proof.
apply tfpsP => i; rewrite leqn0 => /eqP ->.
by rewrite -!coefs_projE coeftC.
Qed.

Local Notation "''X" := (locked (@fps_poly 'X)).
Local Notation "'''X^' n" := (''X ^+ n).

Lemma proj_fpsX n : 'pi_n ''X = (\X)%tfps.
Proof. by rewrite -lock piindE. Qed.
Lemma proj_fpsXn n i : 'pi_n ''X^i = (\X)%tfps^+i.
Proof. by rewrite proj_simp proj_fpsX. Qed.
Lemma coef_fpsX i : (''X ``_i) = (i == 1%N)%:R :> R.
Proof. by rewrite -lock coefs_fps_poly coefX. Qed.
Lemma coef_fpsXn n i : (''X^n ``_i) = (i == n)%:R :> R.
Proof. by rewrite -lock -fps_polyX coefs_fps_poly coefXn. Qed.

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
rewrite !coefs_projE !proj_simp proj_fpsX coef_tfpsXM leqnn.
by rewrite -coefs_projE coeft_proj // leq_pred.
Qed.

Lemma coef_fpsXnM f k i :
  (''X^k * f)``_i = if (i < k)%N then 0 else f``_(i - k).
Proof.
rewrite !coefs_projE !proj_simp proj_fpsX coef_tfpsXnM leqnn.
by rewrite -coefs_projE coeft_proj // leq_subr.
Qed.

Lemma expr_cX (c : R) i : (c *: ''X) ^+ i = (c ^+ i) *: ''X^i.
Proof.
by apply invlimE => j; rewrite !proj_simp proj_fpsX expr_tfpscX.
Qed.


Lemma fps_def s : s = \fps s``_i .X^i.
Proof. by apply/fpsP => j; rewrite coefs_FPSeries. Qed.

End CoeffSeries.

Arguments fpsC {R}.
Arguments fps_poly {R}.
Notation "c %:S" := (fpsC c).
Notation "''X" := (locked (@fps_poly _ 'X)).
Notation "'''X^' n" := (''X ^+ n).

(* I deactivated the coercion because it is too confusing 
Coercion fps_poly_coerce (R : ringType) : polynomial R -> {fps R} := fps_poly.

Lemma fps_polyXE (R : ringType) : ''X = 'X :> {fps R}.
Proof. by unlock. Qed.

Lemma fps_polyXnE (R : ringType) n : ''X^n = 'X^n :> {fps R}.
Proof. by unlock; rewrite -rmorphX. Qed.

Lemma very_confusing (R : ringType) :
  1 + 'X + 'X^2%N = 1 + ''X + ''X^2%N :> {fps R}.
Proof.
by rewrite fps_polyXnE fps_polyXE /fps_poly_coerce /= !rmorphD rmorph1.
Qed.
 *)


Section FpsUnitRing.

Variable R : unitRingType.
Implicit Type f : {fps R}.

Canonical fps_unitRingType :=
  Eval hnf in UnitRingType {fps R} [unitRingMixin of {fps R} by <-].

Lemma unit_fpsE f : (f \is a GRing.unit) = (f``_0 \is a GRing.unit).
Proof.
apply/ilunitP/idP => [/(_ 0%N) | Hu i].
- by rewrite coefs_projE -unit_tfpsE.
- by rewrite unit_tfpsE coeft_proj.
Qed.

Lemma proj_unit_fps f :
  reflect (forall i : nat, 'pi_i f \is a GRing.unit)
          (f \is a GRing.unit).
Proof.
rewrite unit_fpsE; apply (iffP idP) => [fU i| fU].
- by move: fU; rewrite -(coeft_proj (leq0n i)) unit_tfpsE.
- by rewrite coefs_projE -unit_tfpsE.
Qed.
Lemma proj_nunit_fps f :
  reflect (forall i : nat, 'pi_i f \isn't a GRing.unit)
          (f \isn't a GRing.unit).
Proof.
rewrite unit_fpsE; apply (iffP idP) => [fU i| fU].
- by move: fU; rewrite -(coeft_proj (leq0n i)) unit_tfpsE.
- by rewrite coefs_projE -unit_tfpsE.
Qed.

Lemma projV i : {morph 'pi[{fps R}]_i : x / x ^-1 }.
Proof.
move=> f.
case (boolP (f \is a GRing.unit)) => [/rmorphV -> // | ninv].
by rewrite !invr_out // unit_tfpsE coeft_proj // -unit_fpsE.
Qed.

Lemma coefs0V f : (f^-1)``_0 = (f``_0)^-1.
Proof. by rewrite !coefs_projE -coeft0V projV. Qed.

Lemma coefsV f i :
  f \is a GRing.unit ->
  f^-1``_i = if i == 0%N then f``_0 ^-1
             else - (f``_0 ^-1) * (\sum_(j < i) f``_j.+1 * f^-1``_(i - j.+1)).
Proof.
move=> funit.
rewrite coefs_projE projV.
rewrite [LHS](coeftV _ (rmorph_unit _ funit)) // ltnn.
case: eqP => [->| _]; first by rewrite -coefs_projE.
rewrite coeft_proj //; congr (_ * _); apply eq_bigr => [] [j ltji] _.
rewrite !coeft_proj //=; congr (_ * _).
by rewrite -projV //= !coeft_proj // leq_subr.
Qed.

End FpsUnitRing.

Definition proj_simpl :=
  (proj0, projD, projN, projB, projMn, projMNn, proj_sum,
   proj1, projM, projX, proj_prod, projZ, projV,
   proj_fpsX, proj_fpsXn).

Definition coefs_simpl :=
  (coefs0, coefsD, coefsN, coefsB, coefsMn, coefsMNn, coefs_sum,
   coefs1, coefsZ,   coef_fpsX, coef_fpsXn).


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

Canonical fps_comUnitRingType := Eval hnf in [comUnitRingType of {fps R}].
Canonical fps_unitalgType :=     Eval hnf in [unitAlgType R of {fps R}].
Canonical fps_comAlgType :=      Eval hnf in [comAlgType R of {fps R}].
Canonical fps_comUnitAlgType :=  Eval hnf in [comUnitAlgType R of {fps R}].

End FpsComUnitRing.


Section Valuation.

Variable R : ringType.
Implicit Type s : {fps R}.

Definition slead s : R := if valuat s is Nat n then s``_n else 0.

Lemma coefs_proj0 s n : ('pi_n s = 0) <-> (forall i, (i <= n)%N -> s``_i = 0).
Proof.
split => [H0 i lt_in|H0].
- by rewrite -(coeft_proj lt_in) H0 coeft0.
- by apply/tfpsP => j le_ji; rewrite coeft0 coeft_proj // H0.
Qed.

Variant valuat_spec s : natbar -> Set :=
  | ValNat n of s``_n != 0 & (forall i, (i < n)%N -> s``_i = 0) :
      valuat_spec s (Nat n)
  | ValInf of s = 0 : valuat_spec s Inf.

Lemma valuatP s : valuat_spec s (valuat s).
Proof.
case: (valuatP s) => [/= n Hn0 Hin| ->]; last exact: ValInf.
apply ValNat => [|i iv]; last by rewrite coefs_projE Hin ?coeft0.
move: Hn0; apply contra => /eqP Hn; apply/eqP.
rewrite coefs_proj0 => i; rewrite leq_eqVlt => /orP [/eqP -> //|].
by rewrite coefs_projE => /Hin ->; rewrite coeft0.
Qed.

Lemma coefs_le_valuat s n : (Nat n < valuat s)%O -> s``_n = 0.
Proof.
case: valuatP => [v Hv vmin /= |->]; last by rewrite coefs0.
by rewrite ltEnatbar; apply: vmin.
Qed.

Lemma valuatNatE s n :
  s``_n != 0 -> (forall i, (i < n)%N -> s``_i = 0) -> valuat s = Nat n.
Proof.
move => Hn0 H0; apply: valuatNatE.
- by move: Hn0; apply contra => /eqP; rewrite coefs_proj0 => ->.
- move=> i lt_in; rewrite coefs_proj0 => j le_ji.
  exact: (H0 j (leq_ltn_trans le_ji lt_in)).
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

Lemma slead0 : slead 0 = 0.
Proof. by rewrite /slead valuat0. Qed.

Lemma valuat_fpsC c : valuat (c%:S : {fps R}) = if c == 0 then Inf else Nat 0.
Proof.
case: (altP (c =P 0)) => [->|Hc]/=; first by rewrite fpsC0 valuat0.
by apply valuatNatE; rewrite // coefsC.
Qed.
Lemma slead_coefsC c : slead c%:S = c.
Proof.
by rewrite /slead valuat_fpsC; case: eqP => [->|_]; rewrite ?coefsC.
Qed.

Lemma slead1 : slead 1 = 1.
Proof. by rewrite /slead valuat1 coefs1. Qed.

Lemma valuatInfE s : (s == 0 :> {fps R}) = (valuat s == Inf).
Proof. by rewrite valuat0P. Qed.
Lemma slead0E s : (s == 0 :> {fps R}) = (slead s == 0).
Proof.
rewrite /slead; case: valuatP => [n Hn _|->]; last by rewrite !eqxx.
rewrite (negbTE Hn); apply/contraNF: Hn => /eqP ->.
by rewrite coefs0.
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

Lemma valuatXn n : valuat (''X ^+ n : {fps R}) = Nat n.
Proof. by rewrite -(mulr1 (''X ^+ n)) valuatXnM valuat1 /= addn0. Qed.
Lemma sleadXn n : slead (''X ^+ n  : {fps R}) = 1.
Proof. by rewrite /slead valuatXn coef_fpsXn eqxx. Qed.

Lemma valuatX : valuat (''X : {fps R}) = Nat 1.
Proof. by rewrite -valuatXn expr1. Qed.
Lemma sleadX : slead (''X : {fps R}) = 1.
Proof. by rewrite /slead valuatX coef_fpsX eqxx. Qed.

Lemma sleadDr s1 s2 :
  (valuat s1 < valuat s2)%O -> slead (s1 + s2) = slead s1.
Proof.
rewrite /slead => H; rewrite (valuatDr H).
move: H; case: (valuat s1) => // v.
case: (valuatP s2) => [v2 _ v2min | -> _]; last by rewrite addr0.
by rewrite coefsD ltEnatbar => /v2min ->; rewrite addr0.
Qed.

Lemma sleadBr s1 s2 :
  (valuat s1 < valuat s2)%O -> slead (s1 - s2) = slead s1.
Proof. by rewrite -(valuatN s2); apply sleadDr. Qed.

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
Proof. exact: (big_morph _ valuatM (valuat1 _)). Qed.

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


Section MapFPS.

Variables (K L : ringType) (n : nat) (F : {rmorphism K -> L}).

Implicit Type g h : {fps K}.

Definition map_fps g : {fps L} := FPSeries (F \o seriesfun g).

Lemma coef_map_fps i g : (map_fps g)``_i = F (g``_i).
Proof. by rewrite coefs_FPSeries unlock. Qed.

Lemma proj_map_fps i g : 'pi_i (map_fps g) = map_tfps F ('pi_i g).
Proof.
apply/tfpsP => j le_ji.
by rewrite coeft_proj // coef_map_fps coef_map_tfps coeft_proj.
Qed.

Lemma compat_map_fps :
  cone (fps_invsys L) (fun i => map_tfps F \o 'pi[{fps K}]_i).
Proof. by move=> g i j le_ij /=; rewrite -!proj_map_fps /= ilprojE. Qed.

Lemma map_fps_indE : map_fps = 'ind compat_map_fps.
Proof.
by apply: funext => g; apply: ind_uniq => i {}g /=; apply: proj_map_fps.
Qed.

Fact map_fps_is_additive : additive map_fps.
Proof. by rewrite map_fps_indE => f g; rewrite rmorphB. Qed.
Canonical map_fps_additive :=
  Eval hnf in Additive map_fps_is_additive.

Lemma map_fpsZ (c : K) g : map_fps (c *: g) = (F c) *: (map_fps g).
Proof.
by apply/invlimE => i; rewrite !(linearZ, proj_map_fps) /= proj_map_fps.
Qed.
Canonical map_fps_linear :=
  Eval hnf in AddLinear (map_fpsZ : scalable_for (F \; *:%R) map_fps).

Fact map_fps_is_multiplicative : multiplicative map_fps.
Proof.
rewrite map_fps_indE.
by split; [move=> f g; rewrite rmorphM | rewrite rmorph1].
Qed.
Canonical map_fps_rmorphism :=
  Eval hnf in AddRMorphism map_fps_is_multiplicative.
Canonical map_fps_lrmorphism :=
  Eval hnf in [lrmorphism of map_fps].

(* Tests *)
Example test_map_tfps0 : map_fps 0 = 0.
Proof. by rewrite linear0. Qed.

Example test_map_tfpsD g h :
  map_fps (g + h) = (map_fps g) + (map_fps h).
Proof. by rewrite linearD. Qed.

End MapFPS.

Lemma map_fps_injective (K L : ringType) (F : {rmorphism K -> L}) :
  injective F -> injective (@map_fps _ _ F).
Proof.
move=> Finj x y eqmap; apply/invlimE => i.
by apply: (map_tfps_injective Finj); rewrite -!proj_map_fps eqmap.
Qed.

Lemma map_fps_inj (K : fieldType) (L : ringType) (F : {rmorphism K -> L}) :
  injective (@map_fps _ _ F).
Proof.
move=> x y eqmap; apply/invlimE => i.
by apply: (map_tfps_inj (F := F)); rewrite -!proj_map_fps eqmap.
Qed.

Lemma map_fps_idfun (K : fieldType) :
  map_fps [rmorphism of (@idfun K)] =1 @idfun {fps K}.
Proof.
move=> x; apply/invlimE => i.
by rewrite proj_map_fps map_tfps_idfun.
Qed.



Section Coefficient01.

Variables (R : ringType).
Implicit Types (f g : {fps R}).

Definition coefs0_eq0 := fun f : {fps R} => f``_0 == 0.
Definition coefs0_eq1 := fun f : {fps R} => f``_0 == 1.

Lemma coefs0_eq0E f : (f \in coefs0_eq0) = (f``_0 == 0).
Proof. by rewrite -topredE. Qed.

Lemma coefs0_eq1E f : (f \in coefs0_eq1) = (f``_0 == 1).
Proof. by rewrite -topredE. Qed.

Lemma proj_coefs0_eq0 f :
  reflect (forall i : nat, 'pi_i f \in coeft0_eq0) (f \in coefs0_eq0).
Proof.
rewrite coefs0_eq0E.
by apply (iffP idP) => [f0 i| /(_ 0%N)]; rewrite coeft0_eq0E coeft_proj.
Qed.
Lemma proj_coefs0_neq0 f :
  reflect (forall i : nat, 'pi_i f \notin coeft0_eq0) (f \notin coefs0_eq0).
Proof.
rewrite coefs0_eq0E.
by apply (iffP idP) => [f0 i| /(_ 0%N)]; rewrite coeft0_eq0E coeft_proj.
Qed.

Lemma proj_coefs0_eq1 f :
  reflect (forall i : nat, 'pi_i f \in coeft0_eq1) (f \in coefs0_eq1).
Proof.
rewrite coefs0_eq1E.
by apply (iffP idP) => [f0 i| /(_ 0%N)]; rewrite coeft0_eq1E coeft_proj.
Qed.
Lemma proj_coefs0_neq1 f :
  reflect (forall i : nat, 'pi_i f \notin coeft0_eq1) (f \notin coefs0_eq1).
Proof.
rewrite coefs0_eq1E.
by apply (iffP idP) => [f0 i| /(_ 0%N)]; rewrite coeft0_eq1E coeft_proj.
Qed.

Fact coefs0_eq0_idealr : idealr_closed coefs0_eq0.
Proof.
split => [|| a p q ]; rewrite ?coefs0_eq0E ?coefs0 ?coefs1 ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefsD q0_eq0 addr0 coefs0M p0_eq0 mulr0.
Qed.

Fact coefs0_eq0_key : pred_key coefs0_eq0. Proof. by []. Qed.

Canonical coefs0_eq0_keyed := Eval hnf in KeyedPred coefs0_eq0_key.
Canonical coefs0_eq0_opprPred := Eval hnf in OpprPred coefs0_eq0_idealr.
Canonical coefs0_eq0_addrPred := Eval hnf in AddrPred coefs0_eq0_idealr.
Canonical coefs0_eq0_zmodPred := Eval hnf in ZmodPred coefs0_eq0_idealr.

Definition coefs0_eq0_ntideal := idealr_closed_nontrivial coefs0_eq0_idealr.
Canonical coefs0_eq0_ideal :=
  Eval hnf in MkIdeal coefs0_eq0_zmodPred coefs0_eq0_ntideal.

Lemma coefs0_eq0Z f c : f \in coefs0_eq0 -> c *: f \in coefs0_eq0.
Proof. by move=> hf; rewrite -mulr_algl idealMr. Qed.

Lemma coefs0_eq0X f i : f \in coefs0_eq0 -> f ^+ i.+1 \in coefs0_eq0.
Proof. by move=> hf; rewrite exprSr idealMr. Qed.

Lemma coefs0_eq10 f : (f \in coefs0_eq1) = ((1 - f) \in coefs0_eq0).
Proof. by rewrite ?coefs0_eq0E ?coefs0_eq1E coefsB coefs1 subr_eq0 eq_sym. Qed.

Lemma coefs0_eq01 f : (f \in coefs0_eq0) = ((1 + f) \in coefs0_eq1).
Proof. by rewrite coefs0_eq10 -[RHS]rpredN !opprD !opprK addKr. Qed.

Lemma coefs0_eq1_add01 f g :
  f \in coefs0_eq0 -> g \in coefs0_eq1 -> f + g \in coefs0_eq1.
Proof.
rewrite coefs0_eq0E !coefs0_eq1E coefsD => /eqP -> /eqP ->.
by rewrite add0r.
Qed.

Lemma fpsX_in_coefs0_eq0 : ''X \in coefs0_eq0.
Proof. by rewrite coefs0_eq0E coef_fpsX. Qed.
Lemma fpscX_in_coefs0_eq0 c : c *: ''X \in coefs0_eq0.
Proof. exact/coefs0_eq0Z/fpsX_in_coefs0_eq0. Qed.

(* tests *)
Example zero_in_coefs0_eq0 : 0 \in coefs0_eq0.
Proof. by rewrite rpred0. Qed.

Example coefs0_eq0D f g :
    f \in coefs0_eq0 -> g \in coefs0_eq0 -> f + g \in coefs0_eq0.
Proof. by move=> hf hg; rewrite rpredD. Qed.

Example coefs0_eq0N f : f \in coefs0_eq0 -> (-f) \in coefs0_eq0.
Proof. by move=> hf; rewrite rpredN. Qed.


Fact mulr_closed_coefs0_eq1 : mulr_closed coefs0_eq1.
Proof.
split=> [|x y]; rewrite !coefs0_eq1E ?coefs1 //.
by rewrite coefs0M; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.
Fact coefs0_eq1_key : pred_key coefs0_eq1. Proof. by []. Qed.
Canonical coefs0_eq1_keyed := Eval hnf in KeyedPred coefs0_eq1_key.
Canonical coefs0_eq1_MulrPred := Eval hnf in MulrPred mulr_closed_coefs0_eq1.

(* Tests *)
Example one_in_coefs0_eq1 : 1 \in coefs0_eq1.
Proof. by rewrite rpred1. Qed.

Example coefs0_eq1M f g :
  f \in coefs0_eq1 -> g \in coefs0_eq1 -> f * g \in coefs0_eq1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

End Coefficient01.
Arguments coefs0_eq0 {R}.
Arguments coefs0_eq1 {R}.

Lemma coefs0_eq0_trXnt (R : ringType) (i : nat) (f : {fps R}) :
  ('pi_i f \in coeft0_eq0) = (f \in coefs0_eq0).
Proof. by rewrite coefs0_eq0E coeft0_eq0E coeft_proj. Qed.

Lemma coefs0_eq1_trXnt (R : ringType) (i : nat) (f : {fps R}) :
  ('pi_i f \in coeft0_eq1) = (f \in coefs0_eq1).
Proof. by rewrite !coefs0_eq1E coeft0_eq1E coeft_proj. Qed.


Section Coefficient01Unit.

Variables (R : unitRingType).
Implicit Types (f g : {fps R}).

Fact invr_closed_coefs0_eq1 : invr_closed (@coefs0_eq1 R).
Proof.
move=> f; rewrite !coefs0_eq1E coefs0V; move/eqP ->.
by rewrite invr1.
Qed.
Canonical coefs0_eq1_DivrPred := Eval hnf in DivrPred invr_closed_coefs0_eq1.

Lemma coefs0_eq1V f : f \in coefs0_eq1 -> f^-1 \in coefs0_eq1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Lemma coefs0_eq1_div f g :
  f \in coefs0_eq1 -> g \in coefs0_eq1 -> f / g \in coefs0_eq1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.

Lemma coefs0_eq1_unit f : f \in coefs0_eq1 -> f \is a GRing.unit.
Proof. by rewrite !coefs0_eq1E unit_fpsE => /eqP ->; apply unitr1. Qed.

End Coefficient01Unit.


Section Coefficient01IDomain.

Variables (R : idomainType).
Implicit Types (f g : {fps R}).

Fact coefs0_eq0_prime : prime_idealr_closed (@coefs0_eq0 R).
Proof.
by move => x y; rewrite -!topredE /= /coefs0_eq0 coefs0M mulf_eq0.
Qed.
Canonical coefs0_eq0_pideal :=
  Eval hnf in MkPrimeIdeal (coefs0_eq0_ideal R) coefs0_eq0_prime.

Example coefs0_eq0_prime_test f g :
  f * g \in coefs0_eq0 -> (f \in coefs0_eq0) || (g \in coefs0_eq0).
Proof. by rewrite prime_idealrM. Qed.

End Coefficient01IDomain.



Section DivisionByX.

Variable R : ringType.

Definition sdivX (f : {fps R}) : {fps R} := \fps f``_i.+1 .X^i.

Lemma coefs_sdivX (f : {fps R}) i : (sdivX f)``_i = f``_i.+1.
Proof. by rewrite coefs_FPSeries. Qed.

Lemma smulXK : cancel ( *%R ''X ) sdivX.
Proof.
move=> f; apply/fpsP => i.
by rewrite coefs_sdivX coef_fpsXM.
Qed.

Lemma sdivXK : {in coefs0_eq0, cancel sdivX ( *%R ''X )}.
Proof.
move=> p Hp.
by apply/fpsP => [[|i]]; rewrite coef_fpsXM coefs_sdivX // (eqP Hp).
Qed.
Lemma sdivXX : sdivX (''X : {fps R}) = 1 :> {fps R}.
Proof. by rewrite -[RHS]smulXK mulr1. Qed.

Fact sdivX_is_linear : linear sdivX.
Proof.
by move=> c f g; apply/fpsP => i; rewrite !(coefs_simpl, coefs_sdivX).
Qed.
Canonical sdivX_additive := Eval hnf in Additive sdivX_is_linear.
Canonical sdivX_linear := Eval hnf in Linear sdivX_is_linear.


Implicit Type f : {fps R}.

Lemma proj_mulXE i f : 'pi_i.+1 (''X * f) = tmulX ('pi_i f).
Proof.
apply/tfpsP => j le_ji1.
rewrite coeft_proj // coef_fpsXM coeft_tmulX coeft_proj //.
by case: j le_ji1.
Qed.

Lemma proj_divXE i f : 'pi_i (sdivX f) = tdivX ('pi_i.+1 f).
Proof.
apply/tfpsP => j le_ji1.
by rewrite coeft_proj // coefs_sdivX coeft_tdivX coeft_proj.
Qed.

End DivisionByX.


Section MapMulfXDivfX.

Variables (K L : ringType) (F : {rmorphism K -> L}) (m : nat) (g : {fps K}).

Lemma map_tfpsXM : map_fps F (''X * g) = ''X * (map_fps F g).
Proof.
apply/fpsP => i.
by rewrite !(coef_fpsXM, coef_map_fps) [LHS]fun_if rmorph0.
Qed.

Lemma map_tfps_sdivX : map_fps F (sdivX g) = sdivX (map_fps F g).
Proof.
apply/fpsP => i.
by rewrite !(coefs_sdivX, coef_map_fps).
Qed.

End MapMulfXDivfX.



Section Derivative.

Variables (R : ringType).
Implicit Types (f g : {fps R}).


Definition deriv_fps f : {fps R} := \fps f``_j.+1 *+ j.+1 .X^j.
Local Notation "f ^` () " := (deriv_fps f).

Lemma coef_deriv_fps f j : (f^`()%fps)``_j = f``_j.+1 *+ j.+1.
Proof. by rewrite coefs_FPSeries. Qed.

Lemma proj_deriv_fps f i : 'pi_i f^`()%fps = ('pi_i.+1 f)^`()%tfps.
Proof.
apply tfpsP => j le_ji.
by rewrite coef_deriv_tfps !coeft_proj // coef_deriv_fps.
Qed.

Lemma compat_deriv_fps :
  cone (fps_invsys R)
       (fun i => (@deriv_tfps _ _) \o 'pi[{fps R}]_i.+1).
Proof.
move=> g i j le_ij /=.
by rewrite -proj_deriv_fps /= ilprojE -proj_deriv_fps.
Qed.

Lemma deriv_fps_indE : deriv_fps = 'ind compat_deriv_fps.
Proof.
by apply: funext => g; apply: ind_uniq => i {}g /=; apply: proj_deriv_fps.
Qed.

Fact deriv_fps_is_additive : additive deriv_fps.
Proof. by rewrite deriv_fps_indE; apply: raddfB. Qed.
Canonical deriv_fps_additive :=
  Eval hnf in Additive deriv_fps_is_additive.
Fact deriv_fps_is_linear : linear deriv_fps.
Proof. by rewrite deriv_fps_indE; apply: linearP. Qed.
Canonical deriv_fps_linear :=
  Eval hnf in Linear deriv_fps_is_linear.

Fact deriv_fps0 : (0 : {fps R})^`()%fps = 0.
Proof. exact: raddf0. Qed.

Lemma deriv_fpsC (c : R) : c%:S^`()%fps = 0.
Proof. by apply fpsP => i; rewrite coef_deriv_fps coefsC coefs0 mul0rn. Qed.

Lemma deriv_fps1 : 1^`()%fps = 0.
Proof. by rewrite -fpsC1 deriv_fpsC. Qed.

Fact derivD_fps f g : (f + g)^`()%fps = f^`()%fps + g^`()%fps.
Proof. exact: raddfD. Qed.

Fact derivZ_fps (c : R) f : (c *: f)^`()%fps = c *: f^`()%fps.
Proof. exact: linearZ. Qed.

End Derivative.

Notation "f ^` () " := (deriv_fps f) : fps_scope.


Section MoreDerivative.

Variables (R : ringType).

Lemma deriv_fpsX : (''X)^`()%fps = 1  :> {fps R}.
Proof.
apply invlimE => i.
by rewrite proj_simpl proj_deriv_fps proj_fpsX deriv_tfpsX.
Qed.

Theorem derivM_fps (f g : {fps R}) :
  (f * g)^`()%fps = f^`()%fps * g + f * g^`()%fps.
Proof.
apply invlimE => i.
rewrite !(proj_simpl, proj_deriv_fps) derivM_tfps /=.
by rewrite -!fps_bondE !ilprojE.
Qed.

(* Noncommutative version *)
Theorem derivX_fps_nc (f : {fps R}) k :
  (f ^+ k)^`()%fps = \sum_(i < k) f ^+ i * f^`()%fps * f ^+ (k.-1 - i).
Proof.
apply invlimE => i.
rewrite !(proj_simpl, proj_deriv_fps) derivX_tfps_nc.
apply eq_bigr => j _.
by rewrite !(proj_simpl, proj_deriv_fps) -!fps_bondE !ilprojE.
Qed.

End MoreDerivative.



Section DerivativeComRing.

Variables (R : comRingType).
Implicit Types (f g : {fps R}).


Theorem derivX_fps f k :
  (f ^+ k)^`()%fps = f ^+ k.-1 * f^`()%fps *+ k.
Proof.
apply invlimE => i.
rewrite !(proj_simpl, proj_deriv_fps) derivX_tfps.
by rewrite -!fps_bondE !ilprojE.
Qed.

Theorem derivX_tfps_bis f k :
  (f ^+ k)^`()%fps = f^`()%fps * f ^+ (k.-1) *+ k.
Proof. by rewrite derivX_fps mulrC. Qed.

End DerivativeComRing.


Section DerivativeUnitRing.

Variables (R : unitRingType).
Implicit Types (f g : {fps R}).

(* Noncommutative version *)
Theorem derivV_fps_nc f :
  f \is a GRing.unit ->
  (f^-1)^`()%fps = - f^-1 * f^`()%fps * f^-1.
Proof.
move=> fU; apply invlimE => i.
rewrite !(proj_simpl, proj_deriv_fps).
rewrite derivV_tfps_nc ?(rmorph_unit _ fU) //=.
by rewrite -!projV -!fps_bondE !ilprojE.
Qed.

End DerivativeUnitRing.


Section DerivativeComUnitRing.

Variables (R : comUnitRingType).
Implicit Types (f g : {fps R}).

Theorem derivV_fps f :
  f \is a GRing.unit -> (f^-1)^`()%fps = - f^`()%fps / (f ^+ 2).
Proof.
move=> fU.
by rewrite derivV_fps_nc // -mulrA mulrC -mulrA !mulrN mulNr -invrM.
Qed.

Theorem deriv_div_fps f g :
  g \is a GRing.unit ->
  (f / g)^`()%fps = (f^`()%fps * g - f * g^`()%fps) / (g ^+ 2).
Proof.
move => fU.
rewrite derivM_fps derivV_fps // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
by rewrite expr2 invrM // mulrA divrr // div1r.
Qed.

End DerivativeComUnitRing.


Section Primitive.

Variables (R : unitRingType).

Definition prim_fps f : {fps R} :=
  \fps f``_j.-1 *+ (j != 0%N) / (j%:R) .X^j.
Local Notation "\int p" := (prim_fps p) (at level 10) : fps_scope.

Lemma coef_prim_fps f j :
  (\int f)%fps``_j = if j == 0%N then 0 else f``_j.-1 / (j%:R).
Proof.
by rewrite coefs_FPSeries; case: j; rewrite //= mulr0n mul0r.
Qed.

Lemma coefs0_prim_fps f : (\int f)%fps``_0%N = 0.
Proof. by rewrite coef_prim_fps eqxx. Qed.

Lemma proj0_prim_fps f : 'pi_0%N (\int f)%fps = 0.
Proof.
apply tfpsP => [[|i]] // _.
by rewrite -coefs_projE coef_prim_fps eqxx coef0.
Qed.
Lemma projS_prim_fps f i : 'pi_i.+1 (\int f)%fps = (\int ('pi_i f))%tfps.
Proof.
apply tfpsP => j le_ji.
rewrite coef_prim_tfps !coeft_proj // coef_prim_fps coef_prim /= coef_poly.
by case: j le_ji => //= j ->.
Qed.


Fact prim_fps_is_linear : linear prim_fps.
Proof.
move=> /= r f g; apply fpsP => i.
rewrite !(coefsD, coefsZ, coefs_FPSeries) !mulrA -mulrDl.
by rewrite mulrnAr -mulrnDl.
Qed.
Canonical prim_fps_additive := Eval hnf in Additive prim_fps_is_linear.
Canonical prim_fps_linear := Eval hnf in Linear prim_fps_is_linear.

(* tests *)
Example prim_fps0 : prim_fps 0 = 0.
Proof. exact: linear0. Qed.

Example prim_fpsD : {morph prim_fps : p q / p + q}.
Proof. exact: linearD. Qed.

End Primitive.


Section PrimitiveUnitRing.

Variable R : unitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Types (f g : {fps R}).

Lemma prim_fpsK : cancel (@prim_fps R) (@deriv_fps R).
Proof.
move=> p; apply/fpsP => n.
rewrite coef_deriv_fps coef_prim_fps /=.
by rewrite -mulr_natr divrK.
Qed.

Lemma deriv_tfpsK :
  {in coefs0_eq0, cancel (@deriv_fps R) (@prim_fps R)}.
Proof.
move=> f; rewrite coefs0_eq0E => /eqP f0_eq0.
apply/fpsP => i.
rewrite coef_prim_fps coef_deriv_fps.
case: i => [|i] /=; first by rewrite f0_eq0.
by rewrite -mulr_natr mulrK.
Qed.

End PrimitiveUnitRing.


Section Composition.

Variables (R : ringType).
Implicit Types (f g : {fps R}).

Lemma compat_comp_fps g :
  cone (fps_invsys R)
       (fun i => (comp_tfps ('pi_i g)) \o 'pi[{fps R}]_i).
Proof.
move=> i j le_ij f /=; rewrite fps_bondE.
by rewrite trXnt_comp -?leEnat // -!fps_bondE !ilprojE.
Qed.

Definition comp_fps g : {fps R} -> {fps R} := 'ind (compat_comp_fps g).

Local Notation "f \oS g" := (comp_fps g f).

Lemma proj_comp_fps i f g :
  'pi_i (f \oS g) = (('pi_i f) \oT ('pi_i g))%tfps.
Proof. exact: piindE. Qed.

Lemma comp_fps_coef0_neq0 f g :
  g \notin coefs0_eq0 -> f \oS g = (f``_0%N)%:S.
Proof.
move/proj_coefs0_neq0 => g0neq0; apply/invlimE => i.
by rewrite piindE /= comp_tfps_coef0_neq0 // coeft_proj // proj_fpsC.
Qed.

Lemma comp_fps0r f : f \oS 0 = (f``_0)%:S.
Proof.
apply/invlimE => i.
by rewrite proj_comp_fps proj0 comp_tfps0r proj_fpsC coeft_proj.
Qed.

Lemma comp_fps0l f : 0 \oS f = 0.
Proof.
apply/invlimE => i.
by rewrite proj_comp_fps proj0 comp_tfps0l.
Qed.

Lemma coef0_comp_fps f g : (f \oS g)``_0 = f``_0.
Proof. by rewrite coefs_projE proj_comp_fps coef0_comp_tfps -coefs_projE. Qed.

Lemma coef_comp_fps_leq k l f g :
  g \in coefs0_eq0 -> (k <= l)%N ->
  (f \oS g)``_k = \sum_(i < l.+1) f``_i * (g ^+ i)``_k.
Proof.
move=> /proj_coefs0_eq0 g0eq0 le_kl.
rewrite -(coeft_proj le_kl) proj_comp_fps (coef_comp_tfps_leq _ _ le_kl) //.
apply eq_bigr => /= [] [i] /=; rewrite ltnS => le_il _.
by rewrite -projX /= !coeft_proj.
Qed.

Lemma coef_comp_fps k f g :
  g \in coefs0_eq0 -> (f \oS g)``_k = \sum_(i < k.+1) f``_i * (g ^+ i)``_k.
Proof. by move=> g0; apply: coef_comp_fps_leq. Qed.

Lemma coefs0_eq0_comp f g : (f \oS g \in coefs0_eq0) = (f \in coefs0_eq0).
Proof. by rewrite !coefs0_eq0E coef0_comp_fps. Qed.

Lemma coefs0_eq1_comp f g : (f \oS g \in coefs0_eq1) = (f \in coefs0_eq1).
Proof. by rewrite !coefs0_eq1E coef0_comp_fps. Qed.

Lemma comp_fpsC f (c : R) : c%:S \oS f = c%:S.
Proof.
apply invlimE => i.
by rewrite proj_comp_fps proj_fpsC comp_tfpsC.
Qed.

Fact comp_fps_is_linear g : linear (comp_fps g).
Proof. exact: ilind_is_linear _ (compat_comp_fps g). Qed.
Canonical comp_fps_additive g := Eval hnf in Additive (comp_fps_is_linear g).
Canonical comp_fps_linear g := Eval hnf in Linear (comp_fps_is_linear g).

Lemma comp_fps1 f : 1 \oS f = 1.
Proof. by apply invlimE => i; rewrite proj_comp_fps proj1 comp_tfps1. Qed.

Lemma comp_fpsCf f (c : R) : f \oS (c%:S) = (f``_0)%:S.
Proof.
apply invlimE => i.
by rewrite proj_comp_fps proj_fpsC comp_tfpsCf proj_fpsC coeft_proj.
Qed.

Lemma comp_fpsXr f : f \oS ''X = f.
Proof.
apply invlimE => i.
by rewrite proj_comp_fps proj_fpsX comp_tfpsXr.
Qed.

Lemma comp_fpsX : {in coefs0_eq0, forall f, ''X \oS f = f}.
Proof.
move=> f /proj_coefs0_eq0 f0eq0; apply invlimE => i.
by rewrite proj_comp_fps proj_fpsX comp_tfpsX.
Qed.

Lemma comp_fpsXn n : {in coefs0_eq0, forall f, ''X ^+ n \oS f = f ^+ n}.
Proof.
move=> f /proj_coefs0_eq0 f0eq0; apply invlimE => i.
by rewrite proj_comp_fps proj_fpsXn comp_tfpsXn // rmorphX.
Qed.

End Composition.

Notation "f \oS g" := (comp_fps g f) : fps_scope.


Section CompUnitRing.

Variables (R : unitRingType).
Implicit Types (f g : {fps R}).

Lemma comp_fps_unitE f g :
  ((f \oS g) \is a GRing.unit)%fps = (f \is a GRing.unit).
Proof. by rewrite !unit_fpsE coef0_comp_fps. Qed.

End CompUnitRing.


Section CompComRing.

Variables (R : comRingType).
Implicit Types (f g h : {fps R}).

Local Open Scope fps_scope.

Fact comp_fps_is_multiplicative f : multiplicative (comp_fps f).
Proof. exact: ilind_is_multiplicative _ (compat_comp_fps f). Qed.
Canonical comp_fps_rmorphism f :=
  Eval hnf in AddRMorphism (comp_fps_is_multiplicative f).
Canonical comp_fps_lrmorphism f :=
  Eval hnf in [lrmorphism of (comp_fps f)].


Lemma comp_fpsA f g h : f \oS (g \oS h) = (f \oS g) \oS h.
Proof. by apply invlimE => i; rewrite !proj_comp_fps comp_tfpsA. Qed.

Lemma coef_comp_fps_cX f c i : (f \oS (c *: ''X))``_i = c ^+ i * f``_i.
Proof.
by rewrite !coefs_projE proj_comp_fps projZ proj_fpsX coef_comp_tfps_cX.
Qed.

Theorem deriv_fps_comp f g :
  f \in coefs0_eq0 -> (g \oS f)^`() = (g^`()%fps \oS f) * f^`()%fps.
Proof.
move=> /proj_coefs0_eq0 f0eq0; apply invlimE => i.
rewrite !(proj_simpl, proj_comp_fps, proj_deriv_fps).
by rewrite deriv_tfps_comp //= -fps_bondE ilprojE.
Qed.

End CompComRing.


Local Open Scope fps_scope.

Section Lagrange.

Variables R : comUnitRingType.
Implicit Type (f g : {fps R}).

Lemma compat_lagrfix :
  cone (fps_invsys R)
       (fun i => if i is i'.+1
                 then (@lagrfix R i') \o 'pi[{fps R}]_i'
                 else fun=> 0).
Proof.
move=> i j le_ij f /=; rewrite fps_bondE.
move: le_ij; rewrite {1}leEnat.
case: i j => [|i] [|j] //; first by rewrite trXnt0.
  move=> _; apply tfpsP => i; rewrite leqn0 => /eqP ->.
  by rewrite coef_trXnt (eqP (coeft0_eq0_lagrfix _)) coeft0.
rewrite ltnS => le_ij.
by rewrite trXnt_lagrfix // -!fps_bondE !ilprojE.
Qed.

Definition lagrfix : {fps R} -> {fps R} := 'ind compat_lagrfix.

Lemma proj0_lagrfix f : 'pi_0%N (lagrfix f) = 0.
Proof. exact: piindE. Qed.

Lemma proj_lagrfix i f : 'pi_i.+1 (lagrfix f) = tfps.lagrfix ('pi_i f).
Proof. exact: piindE. Qed.

Lemma coefs0_eq0_lagrfix f : lagrfix f \in coefs0_eq0.
Proof. by rewrite coefs0_eq0E coefs_projE proj0_lagrfix coeft0. Qed.

Lemma lagrfixP f : lagrfix f = ''X * (f \oS lagrfix f).
Proof.
rewrite /lagrfix; apply/fpsP => [][|i]; rewrite !coef_fpsXM //=.
  by rewrite coefs_projE proj0_lagrfix coeft0.
rewrite !coefs_projE proj_lagrfix.
rewrite proj_comp_fps lagrfixP coeft_tmulX /= piindE /=.
case: i => [|i]; first by rewrite !coef0_comp_tfps.
by rewrite trXnt_lagrfix // -!fps_bondE !ilprojE.
Qed.

Lemma lagrfix_divP f : sdivX (lagrfix f) = f \oS lagrfix f.
Proof. by rewrite {1}lagrfixP smulXK. Qed.
Lemma sdivX_lagrfix_unit g :
  g \is a GRing.unit -> sdivX (lagrfix g) \is a GRing.unit.
Proof.
by move=> gU; rewrite lagrfix_divP unit_fpsE coef0_comp_fps -unit_fpsE.
Qed.

Lemma lagrfix_inv f g :
  g \is a GRing.unit -> f \in coefs0_eq0 ->
  f = ''X * (g \oS f) -> (''X * g^-1) \oS f = ''X.
Proof.
move=> gU f0eq0 feq; rewrite feq.
rewrite rmorphM /= rmorphV //= comp_fpsX ?coefs0_eq0E ?coef_fpsXM // -{2}feq.
by rewrite mulrK // comp_fps_unitE.
Qed.

Lemma lagrfix_invPr g :
  g \is a GRing.unit -> (''X * g^-1) \oS lagrfix g = ''X.
Proof. by move/lagrfix_inv/(_ (coefs0_eq0_lagrfix g))/(_ (lagrfixP g)). Qed.

Definition lagrunit f := (f \in coefs0_eq0) && (sdivX f \is a GRing.unit).
Definition lagrinv f := lagrfix (sdivX f)^-1.

Lemma proj_lagrunit f :
  reflect (forall i, tfps.lagrunit ('pi_i.+1 f)) (lagrunit f).
Proof.
rewrite /lagrunit /tfps.lagrunit; apply (iffP andP) => [|H]; last split.
- move => [/proj_coefs0_eq0 f0eq0 /proj_unit_fps divfU i].
  by apply/andP; split; last by rewrite -proj_divXE.
- apply/proj_coefs0_eq0 => [][|i]; last by have /andP [] := H i.
  by have /andP [] := H 0%N; rewrite !coeft0_eq0E !coeft_proj.
- apply/proj_unit_fps => i.
  by rewrite proj_divXE; have /andP [_] := H i.
Qed.
Lemma proj_lagrinv i f : 'pi_i.+1 (lagrinv f) = tfps.lagrinv ('pi_i.+1 f).
Proof. by rewrite /lagrinv proj_lagrfix projV proj_divXE. Qed.

Lemma lagrfixE f : lagrfix f = lagrinv (''X * f^-1).
Proof. by rewrite /lagrinv smulXK invrK. Qed.

Lemma coef1_comp_fps f g :
  f \in coefs0_eq0 -> g \in coefs0_eq0 -> (f \oS g)``_1 = f``_1 * g``_1.
Proof.
move=> f0 g0.
rewrite coef_comp_fps // big_ord_recl (eqP f0) mul0r add0r.
by rewrite big_ord_recl /= big_ord0 /bump /= -!/(_`_ 1) !add1n addr0.
Qed.

Lemma sdivX_unitE f : (sdivX f \is a GRing.unit) = (f``_1 \is a GRing.unit).
Proof. by rewrite unit_fpsE coefs_sdivX. Qed.

Lemma lagrunit_comp : {in lagrunit &, forall f g, lagrunit (f \oS g) }.
Proof.
move=> f g /proj_lagrunit fU /proj_lagrunit gU; apply/proj_lagrunit => i.
by rewrite proj_comp_fps lagrunit_comp //; [exact: fU i|exact: gU i].
Qed.

Lemma lagrunitV : {in lagrunit, forall f, lagrunit (lagrinv f) }.
Proof.
move=> f /proj_lagrunit fU; apply/proj_lagrunit => i.
by rewrite proj_lagrinv; apply/lagrunitV/(fU i).
Qed.

Lemma lagrinvPr : {in lagrunit, forall f, f \oS (lagrinv f) = ''X }.
Proof.
move=> f /proj_lagrunit fU; apply/(invlim_geE 1%N)=> [][|i] // _.
rewrite proj_comp_fps proj_lagrinv lagrinvPr ?proj_fpsX //.
exact: (fU i).
Qed.

Lemma lagrinvPl : {in lagrunit, forall f, (lagrinv f) \oS f = ''X }.
Proof.
move=> f /proj_lagrunit fU; apply/(invlim_geE 1%N)=> [][|i] // _.
rewrite proj_comp_fps proj_lagrinv lagrinvPl ?proj_fpsX //.
exact: (fU i).
Qed.

Lemma lagrinvPr_uniq f g :
  f \in lagrunit -> f \oS g = ''X -> g = lagrinv f.
Proof.
move=> /proj_lagrunit fU Heq; apply/(invlim_geE 1%N)=> [][|i] // _.
rewrite proj_lagrinv; apply: (lagrinvPr_uniq (fU i)).
by rewrite -proj_comp_fps Heq proj_fpsX.
Qed.

Lemma lagrinvPl_uniq f g :
  f \in lagrunit -> g \oS f = ''X -> g = lagrinv f.
Proof.
move=> /proj_lagrunit fU Heq; apply/(invlim_geE 1%N)=> [][|i] // _.
rewrite proj_lagrinv; apply: (lagrinvPl_uniq (fU i)).
by rewrite -proj_comp_fps Heq proj_fpsX.
Qed.

Lemma lagrinvK : {in lagrunit, involutive lagrinv}.
Proof.
(** Standard group theoretic argument: inverse is involutive *)
move=> f Hf.
by apply/esym/lagrinvPl_uniq; [apply: lagrunitV | apply: lagrinvPr].
Qed.

Lemma lagrfix_invPl :
  {in GRing.unit, forall g, lagrfix g \oS (''X * g^-1) = ''X}.
Proof.
move=> g /proj_unit_fps gU; apply/(invlim_geE 1%N)=> [][|i] // _.
rewrite proj_comp_fps proj_lagrfix proj_mulXE !proj_simpl.
exact: (lagrfix_invPl (gU i)).
Qed.

Lemma lagrfix_uniq g : g \in GRing.unit ->
  forall f, f = ''X * (g \oS f) -> f = lagrfix g.
Proof.
move=> /proj_unit_fps gU f Hf.
apply/(invlim_geE 1%N)=> [][|i] // _; rewrite proj_lagrfix.
apply (lagrfix_uniq (gU i)).
by rewrite {1}Hf proj_mulXE proj_comp_fps -!fps_bondE !ilprojE.
Qed.

End Lagrange.


Section LagrangeTheorem.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Type (f g : {fps R}).

Theorem Lagrange_Bürmann_exp g i k :
  g \in GRing.unit ->
  (k <= i)%N -> ((lagrfix g) ^+ k)``_i *+ i = (g ^+ i)``_(i - k) *+ k.
Proof.
move=> /proj_unit_fps gU; case: i => [|i le_ki1].
  by rewrite leqn0 => /eqP ->; rewrite mulr0n.
rewrite -(coeft_proj (leq_subr k _)) coefs_projE !proj_simpl.
rewrite proj_lagrfix Lagrange_Bürmann_exp // ?le_ki1 //=.
case: k le_ki1 => [|k] //; rewrite ltnS subSS => le_ki.
by rewrite -!projX !coeft_proj ?leq_subr ?(leq_trans (leq_subr _ _)).
Qed.

Theorem coefs_lagrfix g i :
  g \in GRing.unit -> (lagrfix g)``_i.+1 = (g ^+ i.+1)``_i / i.+1%:R.
Proof.
move/Lagrange_Bürmann_exp => /(_ i.+1 _ (ltn0Sn _)).
rewrite subSS subn0 mulr1n expr1 => <-.
by rewrite -mulr_natr mulrK.
Qed.

Theorem Lagrange_Bürmann g h i :
  g \in GRing.unit ->
  (h \oS lagrfix g)``_i.+1 = (h^`()%fps * g ^+ i.+1)``_i / i.+1%:R.
Proof.
move=> /proj_unit_fps gU.
rewrite !coefs_projE proj_comp_fps proj_lagrfix Lagrange_Bürmann //.
by rewrite !proj_simpl proj_deriv_fps.
Qed.

Theorem Lagrange_Bürmann2 g h i :
  g \in GRing.unit ->
  (h \oS lagrfix g)``_i = ((1 - ''X * g^`()%fps / g) * h * g ^+ i)``_i.
Proof.
move=> /proj_unit_fps gU.
rewrite -(coeft_proj (leqnSn _)) proj_comp_fps.
have:= Lagrange_Bürmann2 nat_unit ('pi_i.+1 h) i (gU i.+1).
rewrite -proj_lagrfix -fps_bondE ilprojE => ->.
rewrite [''X * _]lock -(coeft_proj (leqnSn _)) !proj_simpl.
by rewrite -lock proj_mulXE -proj_deriv_fps.
Qed.

Theorem Lagrange_Bürmann_exp2 g i k :
  g \in GRing.unit ->
  ((lagrfix g) ^+ k)``_i = ((1 - ''X * g^`()%fps / g) * ''X ^+ k * g ^+ i)``_i.
Proof.
move/Lagrange_Bürmann2 => <-.
by rewrite comp_fpsXn ?coefs0_eq0_lagrfix.
Qed.

End LagrangeTheorem.


Section ExpLog.

Variables (R : unitRingType).
Implicit Types (f g : {fps R}) (i : nat).

Definition exps : {fps R} := \fps i`!%:R ^-1 .X^i.
Definition logs : {fps R} :=     (* This is - log (1 - X) *)
  \fps if i != 0%N then i%:R ^-1 else 0 .X^i.

Definition exp f : {fps R} := exps \oS f.
Definition log f : {fps R} := - logs \oS (1 - f).
Definition expr_fps (c : R) f := exp (c *: log f).

Lemma expsE : exps = exp ''X.
Proof. by rewrite /exp comp_fpsXr. Qed.
Lemma logtE : logs = - log (1 - ''X).
Proof. by rewrite /log raddfN opprK opprB addrC subrK /= comp_fpsXr. Qed.

Lemma proj_exps i : 'pi_i exps = expt.
Proof.
apply tfpsP => j le_ji.
by rewrite coeft_proj // coef_tfps_of_fun le_ji coefs_FPSeries.
Qed.
Lemma proj_exp i f : 'pi_i (exp f) = tfps.exp ('pi_i f).
Proof. by rewrite /exp proj_comp_fps proj_exps. Qed.

Lemma proj_logs i : 'pi_i logs = logt.
Proof.
apply tfpsP => j le_ji.
by rewrite coeft_proj // coef_tfps_of_fun le_ji coefs_FPSeries.
Qed.
Lemma proj_log i f : 'pi_i (log f) = tfps.log ('pi_i f).
Proof. by rewrite /log proj_comp_fps !proj_simpl proj_logs. Qed.

Lemma proj_expr_fps i c f : 'pi_i (expr_fps c f) = expr_tfps c ('pi_i f).
Proof. by rewrite /expr_fps proj_exp projZ proj_log. Qed.

Lemma compat_exp :
  cone (fps_invsys R) (fun i => tfps.exp \o 'pi[{fps R}]_i).
Proof.
move=> i j le_ij f /=; rewrite fps_bondE.
by rewrite trXnt_exp -?leEnat // -!fps_bondE !ilprojE.
Qed.
Lemma exp_indE : exp = 'ind compat_exp.
Proof. by apply: funext=> g; apply: ind_uniq=> i {}g /=; apply: proj_exp. Qed.

Lemma compat_log :
  cone (fps_invsys R) (fun i => tfps.log \o 'pi[{fps R}]_i).
Proof.
move=> i j le_ij f /=; rewrite fps_bondE.
by rewrite trXnt_log -?leEnat // -!fps_bondE !ilprojE.
Qed.
Lemma log_indE : log = 'ind compat_log.
Proof. by apply: funext=> g; apply: ind_uniq=> i {}g /=; apply: proj_log. Qed.


Lemma coefs0_exps : exps``_0 = 1.
Proof. by rewrite coefs_FPSeries fact0 invr1. Qed.
Lemma exps_in_coefs0_eq1 : exps \in coefs0_eq1.
Proof. by rewrite coefs0_eq1E coefs0_exps. Qed.

Lemma coefs0_exp f : (exp f)``_0 = 1.
Proof. by rewrite /exp coef0_comp_fps coefs0_exps. Qed.
Lemma exp_in_coefs0_eq1 f : exp f \in coefs0_eq1.
Proof. by rewrite coefs0_eq1E coefs0_exp. Qed.
Lemma exp_unit f : exp f \is a GRing.unit.
Proof. exact/coefs0_eq1_unit/exp_in_coefs0_eq1. Qed.

Lemma coefs0_logs : logs``_0 = 0.
Proof. by rewrite coefs_FPSeries. Qed.
Lemma logs_in_coefs0_eq1 : logs \in coefs0_eq0.
Proof. by rewrite coefs0_eq0E coefs0_logs. Qed.

Lemma coefs0_log f : (log f)``_0 = 0.
Proof. by rewrite /log coef0_comp_fps coefsN coefs0_logs oppr0. Qed.
Lemma log_in_coefs0_eq0 f : log f \in coefs0_eq0.
Proof. by rewrite coefs0_eq0E coefs0_log. Qed.

Lemma exp_coefs0_isnt_0 f : f \notin coefs0_eq0 -> exp f = 1.
Proof.
rewrite /exp => /comp_fps_coef0_neq0 ->.
by rewrite coefs_FPSeries /= fact0 invr1 fpsC1.
Qed.

Lemma exp0 : exp 0 = 1.
Proof. by rewrite /exp comp_fps0r coefs0_exps fpsC1. Qed.

Lemma expC (c : R) : exp (c%:S) = 1.
Proof.
case (boolP (c%:S \in coefs0_eq0)) => [| p0N0].
- rewrite coefs0_eq0E coefsC /= => /eqP ->.
  by rewrite fpsC0 exp0.
- exact: exp_coefs0_isnt_0.
Qed.


Lemma log_coefs0_isnt_1 f : f \notin coefs0_eq1 -> log f = 0.
Proof.
rewrite /log coefs0_eq10 => /comp_fps_coef0_neq0 ->.
by rewrite coefsN coefs_FPSeries /= oppr0 fpsC0.
Qed.

Lemma log1 : log 1 = 0.
Proof. by rewrite /log subrr comp_fps0r coefsN coefs0_logs oppr0 fpsC0. Qed.

End ExpLog.
Arguments logs {R}.
Arguments exps {R}.
Arguments log {R}.
Arguments exp {R}.
Notation "f ^^ r" := (expr_fps r f) : fps_scope.
Notation "\sqrt f" := (f ^^ (2%:R^-1)) : fps_scope.


Import TFPSUnitRing.

Section ExpMorph.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Types (f g : {fps R}).

Theorem expD : {in @coefs0_eq0 R &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g /proj_coefs0_eq0 f0eq0 /proj_coefs0_eq0 g0eq0; apply invlimE => i.
by rewrite !(proj_simpl, proj_exp) TFPSUnitRing.expD.
Qed.

Lemma expN f : f \in coefs0_eq0 -> exp (- f) = (exp f)^-1.
Proof.
move=> f0_eq0; apply: (@mulrI _ (exp f)); rewrite ?divrr ?exp_unit //.
by rewrite -expD ?rpredN // subrr exp0.
Qed.

Lemma expB : {in @coefs0_eq0 R &, {morph exp : f g / f - g >-> f / g}}.
Proof. by move=> f g hf hg; rewrite expD ?rpredN // expN. Qed.

End ExpMorph.


Section MoreDerivative.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Types (f g : {fps R}).

Theorem derivXn_fps m :
  m != 0%N ->  {in GRing.unit, forall f,
     (f ^- m)^`()%fps = f ^- m.+1 * f^`()%fps *- m}.
Proof.
move=> Hm /= f fU; rewrite -exprVn derivX_fps derivV_fps //.
rewrite !exprVn [_/_]mulrC mulrA mulrN mulNrn -!mulrnAr.
rewrite -!exprVn -exprD -addSnnS addn1.
by case: m Hm.
(** Alternative proof using inverse limits
move=> Hm /= f fU; apply invlimE => i.
rewrite rmorphMNn rmorphM /= !proj_deriv_fps.
(** Why the canonical doesn't work with rmorphV ??? *)
rewrite -!exprVn !rmorphX /= !(rmorphV [rmorphism of 'pi[{fps R}]_ _] fU) /=.
rewrite !exprVn derivXn_tfps //=; last by move: fU => /proj_unit_fps/(_ i.+1).
by rewrite -fps_bondE ilprojE. *)
Qed.

Lemma deriv_fps_eq0_cst f : f^`()%fps = 0 -> {c : R | f = c %:S}.
Proof.
move=> dev0; exists (f``_0).
apply/fpsP => [] [|i]; rewrite coefsC //.
apply: (mulIr (nat_unit i)); rewrite mul0r.
move: dev0 => /(congr1 (fun x : {fps _ } => x``_i)).
by rewrite coef_deriv_fps coefs0 -mulr_natr.
Qed.

Lemma deriv_fps_eq0 f : f^`()%fps = 0 -> f``_0 = 0 -> f = 0.
Proof.
move=> /deriv_fps_eq0_cst [c ->].
by rewrite coefsC /= => ->; rewrite fpsC0.
Qed.

Lemma deriv_fps_eq f g : f^`()%fps = g^`()%fps -> f``_0 = g``_0 -> f = g.
Proof.
move=> eqdev eqc0.
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_fps_eq0; first by rewrite linearB /= eqdev subrr.
by rewrite coefsB eqc0 subrr.
Qed.

End MoreDerivative.

Open Scope fps_scope.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Type (f g : {fps R}).

Lemma deriv_exps : exps^`() = exps :> {fps R}.
Proof.
by apply/invlimE => i; rewrite proj_deriv_fps !proj_exps deriv_expt.
Qed.

Lemma deriv_expE a f :
  f^`() = a *: f -> f = f``_0 *: exp (a *: ''X).
Proof.
move=> devf; apply/invlimE => [][|i].
  by rewrite projZ !proj0CE coefs0_exp tfpsC1 alg_tfpsC.
rewrite (deriv_expE nat_unit (f := 'pi_i.+1 f) (a := a)); first last.
  have:= congr1 'pi[{fps R}]_i devf.
  by rewrite -!fps_bondE !ilprojE proj_deriv_fps projZ.
by rewrite !proj_simpl coeft_proj // proj_exp proj_simpl proj_fpsX.
Qed.

Lemma deriv_expsE f : f^`() = f -> f = f``_0 *: exps.
Proof. by have:= @deriv_expE 1 f; rewrite !scale1r /exp comp_fpsXr. Qed.

Lemma deriv_logs : logs^`() = (1 - ''X)^-1 :> {fps R}.
Proof.
apply/fpsP => /= i.
by rewrite !coefs_projE !proj_simpl proj_deriv_fps proj_logs deriv_logt.
Qed.

Theorem deriv_exp f :
  f \in coefs0_eq0 -> (exp f)^`()%fps = f^`()%fps * (exp f).
Proof. by move=> f0eq0; rewrite /exp deriv_fps_comp // mulrC deriv_exps. Qed.

Theorem deriv_log f :
  f \in coefs0_eq1 -> (log f)^`()%fps = f^`()%fps / f.
Proof.
move=> /proj_coefs0_eq1 f0eq1.
apply/fpsP => /= i.
rewrite !coefs_projE !proj_simpl proj_deriv_fps proj_log deriv_log //=.
by rewrite -!fps_bondE !ilprojE proj_deriv_fps.
Qed.

Lemma expsK : log exps = ''X :> {fps R}.
Proof.
apply/invlimE => i.
by rewrite proj_simpl proj_log proj_exps exptK.
Qed.

Lemma expK : {in @coefs0_eq0 R, cancel exp log}.
Proof.
move=> f /proj_coefs0_eq0 f0_eq0 /=; apply/invlimE => i.
by rewrite proj_log proj_exp expK.
Qed.

Lemma exp_inj : {in @coefs0_eq0 R &, injective exp}.
Proof. exact: (can_in_inj expK). Qed.

Lemma logK : {in @coefs0_eq1 R, cancel log exp}.
Proof.
move=> f /proj_coefs0_eq1 f0_eq1 /=; apply/invlimE => i.
by rewrite proj_exp proj_log logK.
Qed.

Lemma log_inj : {in @coefs0_eq1 R &, injective log}.
Proof.
move=> f g /proj_coefs0_eq1 f0_eq1 /proj_coefs0_eq1 g0_eq1 /= Hlog.
apply/invlimE => i; apply: log_inj => //.
by rewrite -!proj_log Hlog.
Qed.

Lemma logM : {in @coefs0_eq1 R &, {morph log : f g / f * g >-> f + g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
apply exp_inj; rewrite ?rpredD ?log_in_coefs0_eq0 //.
rewrite expD ?log_in_coefs0_eq0 //.
by rewrite !logK // rpredM.
Qed.

Lemma logV : {in @coefs0_eq1 R, {morph log : f / f^-1 >-> - f}}.
Proof.
move=> f f0_eq1 /=.
apply exp_inj; rewrite ?rpredN ?log_in_coefs0_eq0 //.
rewrite expN ?log_in_coefs0_eq0 //.
by rewrite !logK // rpredV.
Qed.

Lemma log_div : {in @coefs0_eq1 R &, {morph log : f g / f / g >-> f - g}}.
Proof. by move=> f g f0_eq1 g0_eq1 /=; rewrite logM ?rpredV // logV. Qed.


Section ExprFPS.

Variable f : {fps R}.
Hypothesis f0_eq1 : f \in coefs0_eq1.

Let log_coefs0_eq0Z c : c *: log f \in coefs0_eq0.
Proof. by rewrite coefs0_eq0Z // log_in_coefs0_eq0. Qed.

Lemma coefs0_eq1_expr c : f ^^ c \in coefs0_eq1.
Proof. by rewrite /expr_tfps exp_in_coefs0_eq1. Qed.

Lemma expr_fps0 : f ^^ 0 = 1.
Proof. by rewrite /expr_fps scale0r exp0. Qed.

Lemma expr_fps1 : f ^^ 1 = f.
Proof. by rewrite /expr_fps scale1r logK. Qed.

Lemma expr_fpsn m : f ^^ m%:R = f ^+ m.
Proof.
elim: m => [|m IHm]; first exact: expr_fps0.
rewrite /expr_fps -{1}add1n natrD scalerDl scale1r expD ?log_in_coefs0_eq0 //.
by rewrite -/(expr_fps _ _) {}IHm logK // exprS.
Qed.

Lemma expr_fpsN a : f ^^ (- a) = (f ^^ a)^-1.
Proof. by rewrite /expr_fps scaleNr expN. Qed.

Lemma expr_fpsN1 : f ^^ (-1) = f ^-1.
Proof. by rewrite expr_fpsN expr_fps1. Qed.

Lemma expr_fpsD a b : f ^^ (a + b) = (f ^^ a) * (f ^^ b).
Proof. by rewrite /expr_fps scalerDl expD. Qed.

Lemma expr_fpsB a b : f ^^ (a - b) = (f ^^ a) / (f ^^ b).
Proof. by rewrite expr_fpsD expr_fpsN. Qed.

Lemma expr_fpsM a b : f ^^ (a * b) = (f ^^ a) ^^ b.
Proof. by rewrite /expr_fps expK ?scalerA ?[b * a]mulrC. Qed.

Lemma deriv_expr_fps a :
  (f ^^ a)^`() = a *: (f ^^ (a - 1)) * f^`()%fps.
Proof.
rewrite {1}/expr_fps deriv_exp //.
rewrite linearZ /= deriv_log // -!scalerAl; congr (_ *: _).
rewrite -mulrA mulrC; congr (_ * _).
by rewrite mulrC expr_fpsB expr_fps1.
Qed.

End ExprFPS.

Lemma expr_fpsNn f m : f \in coefs0_eq1 -> f ^^ (-m%:R) = f ^- m.
Proof.
move=> Hf.
by rewrite -mulN1r expr_fpsM expr_fpsN1 ?expr_fpsn ?exprVn ?rpredV.
Qed.

Lemma expr_fpsK a : a \is a GRing.unit ->
  {in coefs0_eq1, cancel (@expr_fps R a) (@expr_fps R a^-1)}.
Proof. by move=> aU f f0_eq1; rewrite -expr_fpsM divrr ?expr_fps1. Qed.

Lemma expr_fps_inj a : a \is a GRing.unit ->
  {in coefs0_eq1 &, injective (@expr_fps R a)}.
Proof. by move=> /expr_fpsK/can_in_inj. Qed.

Lemma proj_sqrt (i : nat) f : 'pi_i (\sqrt f) = (\sqrt ('pi_i f))%tfps.
Proof. exact: proj_expr_fps. Qed.

Lemma sqrrK f : f \in coefs0_eq1 -> \sqrt (f ^+ 2) = f.
Proof.
by move => Hh; rewrite -expr_fpsn -?expr_fpsM ?divrr ?expr_fps1.
Qed.

Lemma sqrtK f : f \in coefs0_eq1 -> (\sqrt f) ^+ 2 = f.
Proof.
move => Hh; rewrite -expr_fpsn ?coefs0_eq1_expr //.
by rewrite -?expr_fpsM // mulrC divrr ?expr_fps1.
Qed.

End DerivExpLog.


Section CoefExpX.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma coefs1cX c : 1 + c *: ''X \in @coefs0_eq1 R.
Proof.
by rewrite coefs0_eq1E !coefs_simpl /= mulr0 addr0.
Qed.

Lemma deriv1cX c : (1 + c *: ''X)^`()%fps = c%:S :> {fps R}.
Proof.
by rewrite derivD_fps deriv_fps1 add0r derivZ_fps -alg_fpsC deriv_fpsX.
Qed.

Theorem coef_expr1cX c a m :
  ((1 + c *: ''X) ^^ a)%fps``_m =
  c ^+ m * \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof. by rewrite coefs_projE proj_expr_fps !proj_simpl coef_expr1cX. Qed.

Lemma coef_expr1X a m :
  ((1 + ''X) ^^ a)%fps``_m = \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
by rewrite -[''X]scale1r coef_expr1cX // expr1n mul1r.
Qed.

End CoefExpX.

Open Scope fps_scope.

Section SquareRoot.

Variables R : idomainType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Implicit Types (f g : {fps R}).

(* Lifting from TFPS is more complicated than re-doing the computation *)
Lemma sqrtE f g : f \in coefs0_eq1 -> g ^+ 2 = f ->
  g = \sqrt f  \/  g = - \sqrt f.
Proof.
move=> /eqP f0_eq1 Heq.
have /eqP := (congr1 (fun f : {fps R} => f``_0) Heq).
rewrite -subr_eq0 {}f0_eq1 expr2 coefs0M -expr2 subr_sqr_1.
rewrite mulf_eq0 => /orP [].
- by rewrite subr_eq0 -coefs0_eq1E -{}Heq {f} => Hg0; left; rewrite sqrrK.
- rewrite addr_eq0 -eqr_oppLR -coefsN -coefs0_eq1E -{}Heq {f} => Hg0.
  by right; apply oppr_inj; rewrite /= linearN /= opprK -sqrrN sqrrK.
Qed.

End SquareRoot.
