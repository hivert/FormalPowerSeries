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

Require Import natbar.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Order.Def.
Import Order.Syntax.
Import Order.Theory.



Reserved Notation "{ 'series' T }" (at level 0, format "{ 'series'  T }").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\series E .X^ i"
  (at level 36, E at level 36, i at level 50, format "\series  E  .X^ i").
Reserved Notation "''X" (at level 0).
Reserved Notation "'''X^' n" (at level 3, n at level 2, format "'''X^' n").
Reserved Notation "a ^`` ()" (at level 8, format "a ^`` ()").
Reserved Notation "s ``_ i" (at level 3, i at level 2, left associativity,
                            format "s ``_ i").
Reserved Notation "\Sum_( i : t ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i  :  t )  F").
Reserved Notation "\Sum_( i ) F"
         (at level 41, F at level 41, i at level 50,
         format "\Sum_( i )  F").

Local Open Scope ring_scope.
Local Notation simp := Monoid.simpm.


Section DefType.

Variable R : ringType.

(* I'd rather not add a coercion here ! It is redundant with the
   notation p``_i which is very confusing *)
Record fpseries := FPSeries { seriesfun : nat -> R }.

Canonical fpseries_eqType :=
  EqType fpseries gen_eqMixin.
Canonical fpseries_choiceType :=
  ChoiceType fpseries gen_choiceMixin.

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

End DefType.

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


Section FPSDef.

Variable R : ringType.

Implicit Types (a b c: R) (s t u : {series R}) (p q : {poly R}).

Lemma coefpsE i s : coefs i s = s``_i.
Proof. by []. Qed.

Local Notation "\series E .X^ i" := (@FPSeries R (fun i : nat => E)).

Lemma coefs_series E j : (\series E i .X^i)``_j = E j.
Proof. by rewrite unlock. Qed.

Definition seriesC c : {series R} := \series if i is _.+1 then 0 else c .X^i.
Local Notation "c %:S" := (seriesC c).

Lemma coefsC c i : c%:S``_i = if i == 0%N then c else 0.
Proof. by rewrite coefs_series; case: i. Qed.

Lemma coefsC0 i : 0%:S``_i = 0.
Proof. by rewrite coefs_series; case: i. Qed.

Lemma seriesCK : cancel seriesC (coefs 0).
Proof. by move=> c; rewrite /= coefsC. Qed.

Lemma seriesC_inj : injective seriesC.
Proof. by move=> c1 c2 eqc12; have:= coefsC c2 0; rewrite -eqc12 coefsC. Qed.

Lemma seriesfunP s t : (seriesfun s) =1 (seriesfun t) <-> s = t.
Proof. by rewrite -funeqE; split=> [eq_st | -> //]; apply: seriesfun_inj. Qed.

Lemma seriesP s t : (forall n, s``_n = t``_n) <-> (s = t).
Proof.
rewrite unlock /= -/(seriesfun s =1 seriesfun t) -funeqE.
by split => [/seriesfun_inj | -> //].
Qed.

Lemma seriesfunK s : FPSeries (seriesfun s) = s.
Proof. exact: seriesfun_inj. Qed.


Definition series_poly (p : polynomial R) : fpseries R := \series p`_i .X^i.
Definition poly_series n s : {poly R} := \poly_(i < n) s``_i.

Local Notation SP p := (series_poly p).
Local Notation PS s := (poly_series s).

Lemma coefs_series_poly p i : (SP p)``_i = p`_i.
Proof. by rewrite coefs_series. Qed.

Lemma coefs_poly_series n s i : (PS n s)`_i = if (i < n)%N then s``_i else 0.
Proof. by rewrite coef_poly. Qed.

Lemma series_polyK n p : (n >= size p)%N -> PS n (SP p) = p.
Proof.
move=> /leq_sizeP Hn; apply/polyP => i.
rewrite coefs_poly_series coefs_series_poly.
by case: ltnP => //= ni; rewrite Hn.
Qed.

Lemma series_poly_inj : injective series_poly.
Proof.
move=> p q /(congr1 (PS (maxn (size p) (size q)))).
by rewrite !series_polyK ?leq_maxr ?leq_maxl.
Qed.

Lemma poly_series_eqP s t :
  reflect (forall n, PS n s = PS n t) (s == t).
Proof.
apply (iffP eqP) => [->//| Heq]; apply/seriesP => i.
have cps u : u``_i = (PS i.+1 u)`_i by rewrite coefs_poly_series ltnSn.
by rewrite !cps Heq.
Qed.

Lemma poly_seriesP s t :
  reflect (forall n, (PS n.+1 s)`_n = (PS n.+1 t)`_n) (s == t).
Proof.
apply (iffP eqP) => [->//| Heq]; apply/seriesP => i.
have cps u : u``_i = (PS i.+1 u)`_i by rewrite coefs_poly_series ltnSn.
by rewrite !cps Heq.
Qed.

Lemma poly_seriesC n c : PS n.+1 c%:S = c%:P.
Proof.
apply/polyP => i; rewrite coefs_poly_series coefC coefsC.
by case: i => //= i; rewrite if_same.
Qed.

Lemma series_polyC c : SP c%:P = c%:S.
Proof. by apply/seriesP => n; rewrite coefs_series_poly coefC coefsC. Qed.

End FPSDef.

Coercion series_poly : polynomial >-> fpseries.

Arguments seriesC {R}.
Arguments series_poly {R}.
Arguments poly_series {R}.
Notation "c %:S" := (seriesC c).
Notation "\series E .X^ i" := (@FPSeries _ (fun i : nat => E)).


Section FPSRing.

Variable R : ringType.

Local Notation SP p := (series_poly p).
Local Notation PS s := (poly_series s).

Implicit Types (a b c x y z : R) (s t u v : {series R}) (p q : {poly R}).

(* Zmodule structure for Formal power series *)
Definition add_series_def s t := \series s``_i + t``_i .X^i.
Fact add_series_key : unit. Proof. by []. Qed.
Definition add_series := locked_with add_series_key add_series_def.
Canonical add_series_unlockable := [unlockable fun add_series].

Definition opp_series_def s := \series - s``_i .X^i.
Fact opp_series_key : unit. Proof. by []. Qed.
Definition opp_series := locked_with opp_series_key opp_series_def.
Canonical opp_series_unlockable := [unlockable fun opp_series].

Fact coefs_add_series s t i : (add_series s t)``_i = s``_i + t``_i.
Proof. by rewrite [add_series]unlock coefs_series. Qed.

Fact coefs_opp_series s i : (opp_series s)``_i = - (s``_i).
Proof. by rewrite [opp_series]unlock coefs_series. Qed.

Fact add_seriesA : associative add_series.
Proof. by move=> s t u; apply/seriesP=> i; rewrite !coefs_add_series addrA. Qed.

Fact add_seriesC : commutative add_series.
Proof. by move=> s t; apply/seriesP=> i; rewrite !coefs_add_series addrC. Qed.

Fact add_series0 : left_id 0%:S add_series.
Proof.
by move=> s; apply/seriesP=>[i]; rewrite coefs_add_series coefsC0 add0r.
Qed.

Fact add_seriesN : left_inverse 0%:S opp_series add_series.
Proof.
move=> s; apply/seriesP=> i.
by rewrite coefs_add_series coefs_opp_series coefsC if_same addNr.
Qed.

Definition series_zmodMixin :=
  ZmodMixin add_seriesA add_seriesC add_series0 add_seriesN.
Canonical series_zmodType :=
  Eval hnf in ZmodType {series R} series_zmodMixin.
Canonical fpseries_zmodType :=
  Eval hnf in ZmodType (fpseries R) series_zmodMixin.

(* Properties of the zero series *)
Lemma seriesC0 : 0%:S = 0 :> {series R}. Proof. by []. Qed.

Lemma seriesfun0 : seriesfun (0 : {series R}) = (fun _ => 0).
Proof. by rewrite /= funeqE; case. Qed.

Lemma coefs0 i : (0 : {series R})``_i = 0.
Proof. by rewrite coefsC if_same. Qed.

Lemma coefs_is_additive i : additive (coefs i).
Proof. by move=> s t; rewrite -coefs_opp_series -coefs_add_series. Qed.

Lemma coefsD s t i : (s + t)``_i = s``_i + t``_i.
Proof. exact: coefs_add_series. Qed.
Lemma coefsN s i : (- s)``_i = - (s``_i).
Proof. exact: coefs_opp_series. Qed.
Lemma coefsB s t i : (s - t)``_i = s``_i - t``_i.
Proof. by rewrite coefsD coefsN. Qed.

Canonical coefps_additive i :=
  Additive ((fun s => (coefsB s)^~ i) : additive (coefs i)).

Lemma coefsMn s n i : (s *+ n)``_i = (s``_i) *+ n.
Proof. exact: (raddfMn (coefps_additive i)). Qed.
Lemma coefsMNn s n i : (s *- n)``_i = (s``_i) *- n.
Proof. by rewrite coefsN coefsMn. Qed.
Lemma coefs_sum I (r : seq I) (s : pred I) (F : I -> {series R}) k :
  (\sum_(i <- r | s i) F i)``_k = \sum_(i <- r | s i) (F i)``_k.
Proof. exact: (raddf_sum (coefps_additive k)). Qed.


Lemma seriesC_eq0 (c : R) : (c%:S == 0) = (c == 0).
Proof. by apply/eqP/eqP => [/seriesfunP/(_ 0%N) | ->]. Qed.

Lemma seriesCB : {morph seriesC : a b / a + b}.
Proof. by move=> a b; apply/seriesP=>[[|i]]; rewrite coefsD !coefsC ?addr0. Qed.
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


Fact series_poly_is_additive : additive series_poly.
Proof.
move=> p q; apply/seriesP => n.
by rewrite coefsB !coefs_series coefB.
Qed.
Canonical series_poly_additive := Additive series_poly_is_additive.

Lemma series_polyD p q : SP (p + q) = SP p + SP q.
Proof. exact: raddfD. Qed.
Lemma series_polyN p : SP (- p) = - SP p.
Proof. exact: raddfN. Qed.
Lemma series_polyB p q : SP (p - q) = SP p - SP q.
Proof. exact: raddfB. Qed.
Lemma series_polyMn p n : SP (p *+ n) = (SP p) *+ n.
Proof. exact: raddfMn. Qed.
Lemma series_polyMNn p n : SP (p *- n) = (SP p) *- n.
Proof. exact: raddfMNn. Qed.
Lemma series_poly_sum I (r : seq I) (s : pred I) (F : I -> {poly R}) :
  SP (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) SP (F i).
Proof. exact: raddf_sum. Qed.

Fact poly_series_is_additive d : additive (poly_series d).
Proof.
move=> p q; apply/polyP => n.
by rewrite coefB !coefs_poly_series; case: ltnP => _; rewrite ?subr0 ?coefsB.
Qed.
Canonical poly_series_additive d := Additive (poly_series_is_additive d).

Lemma poly_seriesD d s t : PS d (s + t) = PS d s + PS d t.
Proof. exact: raddfD. Qed.
Lemma poly_seriesN d s : PS d (- s) = - PS d s.
Proof. exact: raddfN. Qed.
Lemma poly_seriesB d s t : PS d (s - t) = PS d s - PS d t.
Proof. exact: raddfB. Qed.
Lemma poly_seriesMn d s n : PS d (s *+ n) = (PS d s) *+ n.
Proof. exact: raddfMn. Qed.
Lemma poly_seriesfMNn d s n : PS d (s *- n) = (PS d s) *- n.
Proof. exact: raddfMNn. Qed.
Lemma poly_series_sum d I (r : seq I) (s : pred I) (F : I -> {series R}) :
  PS d (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) PS d (F i).
Proof. exact: raddf_sum. Qed.



(* Formal power series ring structure. *)

Definition mul_series_def s t :=
  \series \sum_(j < i.+1) s``_j * t``_(i - j) .X^i.
Fact mul_series_key : unit. Proof. by []. Qed.
Definition mul_series := locked_with mul_series_key mul_series_def.
Canonical mul_series_unlockable := [unlockable fun mul_series].

Fact coefs_mul_series s t i :
  (mul_series s t)``_i = \sum_(j < i.+1) s``_j * t``_(i - j).
Proof. by rewrite !unlock. Qed.

Lemma poly_mul_series i n :
  (i < n)%N -> forall s t, (mul_series s t)``_i = ((PS n s) * (PS n t))`_i.
Proof.
move=> Hi s t; rewrite coefs_mul_series coefM; apply eq_bigr => [j] _ /=.
by rewrite !coefs_poly_series !(leq_trans _ Hi) // ltnS leq_subr.
Qed.
(* Get associativity from polynomials *)
Fact mul_seriesA : associative mul_series.
Proof.
move=> s t u; apply/seriesP=> n; rewrite !(poly_mul_series (ltnSn n)).
transitivity ((PS n.+1) s * (PS n.+1) t * (PS n.+1) u)`_n.
  rewrite -mulrA !coefM; apply eq_bigr => [[i Hi] /=] _; congr (_ * _).
  rewrite -poly_mul_series ?ltnS ?leq_subr //.
  by rewrite coefs_poly_series ?ltnS ?leq_subr.
rewrite !coefM; apply eq_bigr => [[i Hi] /=] _; congr (_ * _).
by rewrite -poly_mul_series // coefs_poly_series Hi.
Qed.

Fact mul_1series : left_id 1%:S mul_series.
Proof.
move=> s; apply/seriesP => n; rewrite !(poly_mul_series (ltnSn n)).
by rewrite poly_seriesC mul1r coefs_poly_series ltnSn.
Qed.

Fact mul_series1 : right_id 1%:S mul_series.
Proof.
move=> s; apply/seriesP => n; rewrite !(poly_mul_series (ltnSn n)).
by rewrite poly_seriesC mulr1 coefs_poly_series ltnSn.
Qed.

Fact mul_seriesDl : left_distributive mul_series +%R.
Proof.
move=> s t u; apply/seriesP=> n.
by rewrite coefsD !(poly_mul_series (ltnSn n)) -coefD raddfD /= -mulrDl.
Qed.

Fact mul_seriesDr : right_distributive mul_series +%R.
Proof.
move=> s t u; apply/seriesP=> n.
by rewrite coefsD !(poly_mul_series (ltnSn n)) -coefD raddfD /= -mulrDr.
Qed.

Fact series1_neq0 : 1%:S != 0 :> {series R}.
Proof. by rewrite seriesC_eq0 oner_neq0. Qed.

Definition series_ringMixin :=
  RingMixin mul_seriesA mul_1series mul_series1
            mul_seriesDl mul_seriesDr series1_neq0.

Canonical series_ringType :=
  Eval hnf in RingType {series R} series_ringMixin.
Canonical fpseries_ringType :=
  Eval hnf in RingType (fpseries R) series_ringMixin.


Lemma seriesseq1 :
  seriesfun (1 : {series R}) = (fun i : nat => if i == 0%N then 1%R else 0%R).
Proof. by rewrite /= funeqE; case. Qed.

Lemma coefs1 n : (1 : {series R})``_n = (n == 0%N)%:R.
Proof. by rewrite unlock; case: n. Qed.

Lemma coefsM s t n : (s * t)``_n = \sum_(j < n.+1) s``_j * t``_(n - j).
Proof. exact: coefs_mul_series. Qed.

Lemma coefsMr s t n : (s * t)``_n = \sum_(j < n.+1) s``_(n - j) * t``_j.
Proof.
rewrite !(poly_mul_series (ltnSn n)) coef_mul_poly_rev.
by apply eq_bigr => [[i Hi]] _ /=; rewrite !coefs_poly_series Hi ltnS leq_subr.
Qed.

Lemma coefsCM c s i : (c%:S * s)``_i = c * (s``_i).
Proof.
rewrite coefsM big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefsC !simp.
Qed.

Lemma coefsMC c s i : (s * c%:S)``_i = s``_i * c.
Proof.
rewrite coefsMr big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefsC !simp.
Qed.

Lemma seriesC_mul : {morph seriesC : a b / a * b}.
Proof.
by move=> a b; apply/seriesP=> [[|i]]; rewrite coefsCM !coefsC ?simp.
Qed.

Fact seriesC_multiplicative : multiplicative seriesC.
Proof. by split; first apply: seriesC_mul. Qed.
Canonical seriesC_rmorphism := AddRMorphism seriesC_multiplicative.

Lemma seriesCX n : {morph seriesC : c / c ^+ n}. Proof. exact: rmorphX. Qed.
Lemma seriesC1 : seriesC 1 = 1.                  Proof. exact: rmorph1. Qed.
Lemma seriesCM : {morph seriesC : x y  / x * y}. Proof. exact: rmorphM. Qed.

Fact coefps0_multiplicative : multiplicative (coefs 0 : {series R} -> R).
Proof.
split=> [s t|]; last by rewrite seriesCK.
by rewrite !coefpsE coefsM big_ord_recl big_ord0 addr0.
Qed.

Canonical coefps0_rmorphism := AddRMorphism coefps0_multiplicative.

Fact series_poly_is_rmorphism : rmorphism series_poly.
Proof.
split; first exact: series_poly_is_additive.
split=> [p q|]; apply/seriesP=> i; last first.
  by rewrite coefs_series coef1 coefs1.
rewrite coefsM !coefs_series coefM; apply: eq_bigr => j _.
by rewrite !coefs_series.
Qed.
Canonical series_poly_rmorphism := RMorphism series_poly_is_rmorphism.

Lemma series_polyX n : {morph series_poly : p / p ^+ n}.
Proof. exact: rmorphX. Qed.
Lemma series_poly1 : series_poly 1 = 1.
Proof. exact: rmorph1. Qed.
Lemma series_polyM : {morph series_poly : x y  / x * y}.
Proof. exact: rmorphM. Qed.



(* Algebra structure of formal power series. *)
Definition scale_series_def a (s : {series R}) :=
  \series a * s``_i .X^i.
Fact scale_series_key : unit. Proof. by []. Qed.
Definition scale_series := locked_with scale_series_key scale_series_def.
Canonical scale_series_unlockable := [unlockable fun scale_series].

Fact scale_seriesE a s : scale_series a s = a%:S * s.
Proof.
by apply/seriesP=> n; rewrite [scale_series]unlock coefs_series coefsCM.
Qed.

Fact scale_seriesA a b s :
  scale_series a (scale_series b s) = scale_series (a * b) s.
Proof. by rewrite !scale_seriesE mulrA seriesC_mul. Qed.

Fact scale_1series : left_id 1 scale_series.
Proof. by move=> p; rewrite scale_seriesE mul1r. Qed.

Fact scale_seriesDr a : {morph scale_series a : s t / s + t}.
Proof. by move=> s q; rewrite !scale_seriesE mulrDr. Qed.

Fact scale_seriesDl s : {morph scale_series^~ s : a b / a + b}.
Proof. by move=> a b /=; rewrite !scale_seriesE raddfD mulrDl. Qed.

Fact scale_seriesAl a s t : scale_series a (s * t) = scale_series a s * t.
Proof. by rewrite !scale_seriesE mulrA. Qed.

Definition series_lmodMixin :=
  LmodMixin scale_seriesA scale_1series scale_seriesDr scale_seriesDl.

Canonical series_lmodType :=
  Eval hnf in LmodType R {series R} series_lmodMixin.
Canonical fpseries_lmodType :=
  Eval hnf in LmodType R (fpseries R) series_lmodMixin.
Canonical series_lalgType :=
  Eval hnf in LalgType R {series R} scale_seriesAl.
Canonical fpseries_lalgType :=
  Eval hnf in LalgType R (fpseries R) scale_seriesAl.


Lemma mul_seriesC a s : a%:S * s = a *: s.
Proof. by rewrite -scale_seriesE. Qed.

Lemma alg_seriesC a : a%:A = a%:S :> {series R}.
Proof. by rewrite -mul_seriesC mulr1. Qed.

Lemma coefsZ a s i : (a *: s)``_i = a * s``_i.
Proof. by rewrite -[*:%R]/scale_series [scale_series]unlock coefs_series. Qed.

Canonical coefps_linear i : {scalar {series R}} :=
  AddLinear ((fun a => (coefsZ a) ^~ i) : scalable_for *%R (coefs i)).
Canonical coefp0_lrmorphism := [lrmorphism of coefs 0].


Fact series_poly_is_linear : linear series_poly.
Proof.
move=> i p q; apply/seriesP => n.
by rewrite coefsD coefsZ !coefs_series coefD coefZ.
Qed.

Canonical series_poly_linear := Linear series_poly_is_linear.
Canonical series_poly_lrmorphism := [lrmorphism of series_poly].

Fact poly_series_is_linear d : linear (poly_series d).
Proof.
move=> i s t; apply/polyP => n.
rewrite coefD coefZ !coefs_poly_series.
by case: ltnP => _; rewrite ?mulr0 ?addr0 // coefsD coefsZ.
Qed.
Canonical poly_series_linear d := Linear (poly_series_is_linear d).


(* The indeterminate, at last!                                 *)
(* This is just the polynomial indeterminate coerced to series *)
Local Notation "''X" := (locked (@series_poly R 'X)).
Local Notation "'''X^' n" := (''X ^+ n).

Lemma seriesXE : ''X = 'X.
Proof. by unlock. Qed.
Lemma seriesXnE n : ''X^n = 'X^n.
Proof. by unlock; rewrite series_polyX. Qed.
Lemma coefsX i : (''X ``_i) = (i == 1%N)%:R :> R.
Proof. by rewrite seriesXE coefs_series_poly coefX. Qed.

Lemma coefsXn n i : (''X^n ``_i) = (i == n)%:R :> R.
Proof. by rewrite seriesXnE coefs_series_poly coefXn. Qed.

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


Lemma coefsMX s i : (s * ''X)``_i = (if (i == 0)%N then 0 else s``_i.-1).
Proof.
rewrite coefsMr big_ord_recl coefsX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl  /= !coefsX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite coefsX /= !simp.
Qed.

Lemma coefsXM s i : (''X * s)``_i = (if (i == 0)%N then 0 else s``_i.-1).
Proof. by rewrite -commr_seriesX coefsMX. Qed.

Lemma coefsMXn s n i :
  (s * ''X^n)``_i = (if (i < n)%N then 0 else s``_(i - n)).
Proof.
rewrite coefsMr; case: (ltnP i n) => [iltn|].
- apply big1 => [[j /= Hj]] _; rewrite coefsXn.
  by rewrite (ltn_eqF (leq_trans Hj iltn)) mulr0.
- rewrite -ltnS => nlti1.
  rewrite (bigD1 (Ordinal nlti1)) //= coefsXn eqxx mulr1.
  rewrite big1 ?addr0 // => [[j Hj]]/= /negbTE.
  rewrite coefsXn {1}/eq_op /= => ->.
  by rewrite mulr0.
Qed.

Lemma coefsXnM s n i :
  (''X^n * s)``_i = (if (i < n)%N then 0 else s``_(i - n)).
Proof. by rewrite -commr_seriesXn coefsMXn. Qed.

Lemma lreg_seriesZ_eq0 c s : GRing.lreg c -> (c *: s == 0) = (s == 0).
Proof.
move=> creg; apply/eqP/eqP => [|->]; last by rewrite scaler0.
rewrite -!seriesP => H i.
by have/eqP := H i; rewrite coefs0 coefsZ mulrI_eq0 // => /eqP.
Qed.

Lemma rreg_seriesMC_eq0 c s : GRing.rreg c -> (s * c%:S == 0) = (s == 0).
Proof.
move=> creg; apply/eqP/eqP => [|->]; last by rewrite mul0r.
rewrite -!seriesP => H i.
by have/eqP := H i; rewrite coefs0 coefsMC mulIr_eq0 // => /eqP.
Qed.


(* Lifting a ring predicate to series. *)

Implicit Type S : {pred R}.

Definition seriesOver S :=
  [qualify a s : {series R} | `[forall n, `[< s``_n \in S >] ] ].

Fact seriesOver_key S : pred_key (seriesOver S). Proof. by []. Qed.
Canonical seriesOver_keyed S := KeyedQualifier (seriesOver_key S).

Lemma seriesOverS (S1 S2 : {pred R}) :
  {subset S1 <= S2} -> {subset seriesOver S1 <= seriesOver S2}.
Proof.
move =>sS12 s /forallp_asboolP S1p.
by apply/forallp_asboolP => i; apply: sS12.
Qed.

Section SeriesOverAdd.

Variables (S : {pred R}) (addS : addrPred S) (kS : keyed_pred addS).

Lemma seriesOver0 : 0 \is a seriesOver kS.
Proof. by apply/forallp_asboolP => n; rewrite coefs0 rpred0. Qed.

Lemma seriesOverP {s} : reflect (forall i, s``_i \in kS) (s \in seriesOver kS).
Proof. exact: (iffP forallp_asboolP). Qed.

Lemma seriesOverC c : (c%:S \in seriesOver kS) = (c \in kS).
Proof.
by apply/seriesOverP/idP => [/(_ 0%N)| cS [|i]]; rewrite coefsC //= rpred0.
Qed.

Fact seriesOver_addr_closed : addr_closed (seriesOver kS).
Proof.
split=> [|s t Ss St]; first exact: seriesOver0.
by apply/seriesOverP=> i; rewrite coefsD rpredD ?(seriesOverP _).
Qed.
Canonical seriesOver_addrPred := AddrPred seriesOver_addr_closed.

End SeriesOverAdd.


Fact seriesOverNr S (addS : zmodPred S) (kS : keyed_pred addS) :
  oppr_closed (seriesOver kS).
Proof.
by move=> s /seriesOverP Ss; apply/seriesOverP=> i; rewrite coefsN rpredN.
Qed.
Canonical seriesOver_opprPred S addS kS := OpprPred (@seriesOverNr S addS kS).
Canonical seriesOver_zmodPred S addS kS := ZmodPred (@seriesOverNr S addS kS).

Section SeriesOverSemiring.

Variables (S : {pred R}) (ringS : semiringPred S) (kS : keyed_pred ringS).

Fact seriesOver_mulr_closed : mulr_closed (seriesOver kS).
Proof.
split=> [|s t /seriesOverP Ss /seriesOverP St].
- by rewrite seriesOverC rpred1.
- by apply/seriesOverP=> i; rewrite coefsM rpred_sum // => j _; apply: rpredM.
Qed.
Canonical seriesOver_mulrPred := MulrPred seriesOver_mulr_closed.
Canonical seriesOver_semiringPred := SemiringPred seriesOver_mulr_closed.

Lemma seriesOverZ :
  {in kS & seriesOver kS, forall c s, c *: s \is a seriesOver kS}.
Proof.
by move=> c s Sc /seriesOverP Sp; apply/seriesOverP=> i; rewrite coefsZ rpredM ?Sp.
Qed.

Lemma seriesOverX : ''X \in seriesOver kS.
Proof.
by apply/seriesOverP=> [] [|[|i]]; rewrite coefsX //= ?rpred0 ?rpred1.
Qed.

End SeriesOverSemiring.

Section SeriesOverRing.

Variables (S : {pred R}) (ringS : subringPred S) (kS : keyed_pred ringS).
Canonical seriesOver_smulrPred := SmulrPred (seriesOver_mulr_closed kS).
Canonical seriesOver_subringPred := SubringPred (seriesOver_mulr_closed kS).

End SeriesOverRing.



(** Valuation of a series *)
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
- apply ValInf; apply seriesP => n; rewrite coefs0.
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
- apply: (ValXnNat (t := \series s``_(v + i) .X^i)).
  + by rewrite coefs_series addn0.
  + apply/seriesP => n; rewrite coefsXnM; case: ltnP; first exact: vmin.
    by rewrite coefs_series => /subnKC ->.
- by apply ValXnInf; apply seriesP => n; rewrite coefs0.
Qed.

Lemma valuatXnE s n : s``_0 != 0 -> valuat (''X^n * s) = Nat n.
Proof.
by move=> Hs; apply valuatNatE => [|i Hi]; rewrite coefsXnM ?ltnn ?subnn // Hi.
Qed.

Lemma valuatXn_leP s n :
  reflect (exists t, s = (''X^n) * t) (Nat n <= valuat s)%O.
Proof.
case: valuatXnP => [v t Ht|]->{s}; apply (iffP idP) => //=.
- rewrite leEnatbar => nlev.
  exists (''X^(v - n) * t); rewrite mulrA.
  by rewrite -exprD subnKC //.
- rewrite leEnatbar => [] [s] /(congr1 (coefs v)) /=.
  by apply contra_eqT; rewrite -ltnNge !coefsXnM /= ltnn subnn => ->.
- by move=> _; exists 0; rewrite mulr0.
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite coefs0 eq_refl. Qed.
Lemma slead0 : slead 0 = 0.
Proof. by rewrite /slead valuat0. Qed.

Lemma valuat_seriesC c : valuat c%:S = if c == 0 then Inf else Nat 0.
Proof.
case: (altP (c =P 0)) => [->|Hc]/=; first by rewrite valuat0.
by apply valuatNatE; rewrite // coefsC.
Qed.
Lemma slead_coefsC c : slead c%:S = c.
Proof.
by rewrite /slead valuat_seriesC; case: eqP => [->|_]; rewrite ?coefsC.
Qed.

Lemma valuat1 : valuat 1 = Nat 0.
Proof. by rewrite valuat_seriesC oner_eq0. Qed.
Lemma slead1 : slead 1 = 1.
Proof. by rewrite /slead valuat1 coefs1. Qed.

Lemma valuatInfE s : (s == 0) = (valuat s == Inf).
Proof.
apply/eqP/eqP => [-> |]; first exact: valuat0.
by case: valuatP.
Qed.
Lemma slead0E s : (s == 0) = (slead s == 0).
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

Lemma valuatXnM s n : valuat (''X^n * s) = addbar (Nat n) (valuat s).
Proof.
case: (valuatXnP s) => [v t Ht|]->{s}; last by rewrite mulr0 valuat0.
by rewrite /= mulrA -exprD valuatXnE.
Qed.
Lemma sleadXnM s n : slead (''X^n * s) = slead s.
Proof.
rewrite /slead valuatXnM; case: (valuat s) => //= v.
by rewrite coefsXnM ltnNge leq_addr /= addKn.
Qed.

Lemma valuatXM s : valuat (''X * s) = addbar (Nat 1) (valuat s).
Proof. by rewrite -valuatXnM expr1. Qed.
Lemma sleadXM s : slead (''X * s) = slead s.
Proof.
rewrite /slead valuatXM; case: (valuat s) => //= v.
by rewrite coefsXM add1n.
Qed.

Lemma valuatXn n : valuat ''X^n = Nat n.
Proof. by rewrite -(mulr1 ''X^n) valuatXnM valuat1 /= addn0. Qed.
Lemma sleadXn n : slead ''X^n = 1.
Proof. by rewrite /slead valuatXn coefsXn eqxx. Qed.

Lemma valuatX : valuat ''X = Nat 1.
Proof. by rewrite -valuatXn expr1. Qed.
Lemma sleadX : slead ''X = 1.
Proof. by rewrite /slead valuatX coefsX eqxx. Qed.

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
rewrite /= mulrA (commr_seriesXn v2) mulrA -exprD addnC.
by apply/valuatXn_leP; exists (t1 * t2); rewrite mulrA.
Qed.
End FPSRing.
Notation "''X" := (locked (@series_poly _ 'X)).
Notation "'''X^' n" := (''X ^+ n).

Arguments valuat0 {R}.
Arguments valuat1 {R}.
Arguments slead  {R}.
Arguments slead0 {R}.
Arguments slead1 {R}.



(* Single derivative. *)
Section Derivative.

Variable R : ringType.
Implicit Types (a b c x y z : R) (s t r d : {series R}).

Definition derivs s := \series s``_i.+1 *+ i.+1 .X^i.

Local Notation "a ^`` ()" := (derivs a).

Lemma coefs_deriv s i : s^``()``_i = s``_i.+1 *+ i.+1.
Proof. by rewrite coefs_series. Qed.

Lemma seriesOver_deriv S (ringS : semiringPred S) (kS : keyed_pred ringS) :
  {in seriesOver kS, forall s, s^``() \is a seriesOver kS}.
Proof.
by move=> s /seriesOverP Ks; apply/seriesOverP=> i; rewrite coefs_deriv rpredMn.
Qed.

Lemma derivC c : c%:S^``() = 0.
Proof. by apply/seriesP=> i; rewrite coefs_deriv coefs0 coefsC mul0rn. Qed.

Lemma derivX : ''X ^``() = 1.
Proof. by apply/seriesP=> [[|i]]; rewrite coefs_deriv coefs1 coefsX ?mul0rn. Qed.


(** TODO : move this elsewhere and rename *)
Lemma inv1BcXl c : (1 - c *: ''X) * \series c ^+ i .X^i = 1.
Proof.
apply/seriesP => n; rewrite coefsM big_ord_recl /=.
rewrite !coefsB coefs1 coefsZ coefsX coefs_series /= !simp /= subr0 subn0.
case: n => [|n]; rewrite ?big_ord0 coefs1 /= ?addr0 ?expr0 ?mulr1 //.
rewrite big_ord_recl /bump /= !simp /=.
rewrite coefsB coefs1 coefsZ coefsX coefs_series /= !simp /=.
rewrite subSS subn0 mulNr -exprS subrr add0r.
rewrite /bump /=; apply big1 => [[i /= _] _].
by rewrite !add1n coefsB coefs1 coefsZ coefsX /= !simp mulNr mul0r oppr0.
Qed.

Lemma inv1BcXr c : (\series c ^+ i .X^i) * (1 - c *: ''X) = 1.
Proof.
apply/seriesP => n; rewrite coefsMr big_ord_recl /=.
rewrite !coefsB coefs1 coefsZ coefsX coefs_series /= !simp /= subr0 subn0.
case: n => [|n]; rewrite ?big_ord0 coefs1 /= ?addr0 ?expr0 ?mulr1 //.
rewrite big_ord_recl /bump /= !simp /=.
rewrite coefsB coefs1 coefsZ coefsX coefs_series /= !simp /=.
rewrite subSS subn0 mulrN -exprSr subrr add0r.
rewrite /bump /=; apply big1 => [[i /= _] _].
by rewrite !add1n coefsB coefs1 coefsZ coefsX /= !simp mulrN mulr0 oppr0.
Qed.

Lemma inv1BXl : (1 - ''X) * \series 1 .X^i = 1 :> {series R}.
Proof.
have:= inv1BcXl 1; rewrite !scale1r => {2}<-; congr (_ * _).
by apply/seriesP => n; rewrite !coefs_series expr1n.
Qed.

Lemma inv1BXr : (\series 1 .X^i) * (1 - ''X) = 1 :> {series R}.
Proof.
have:= inv1BcXr 1; rewrite !scale1r => {2}<-; congr (_ * _).
by apply/seriesP => n; rewrite !coefs_series expr1n.
Qed.

Lemma inv1DXl : (1 + ''X) * \series (-1)^+i .X^i = 1 :> {series R}.
Proof. by have:= inv1BcXl (-1); rewrite !scaleN1r opprK. Qed.

Lemma inv1DXr : (\series (-1)^+i .X^i) * (1 + ''X) = 1 :> {series R}.
Proof. by have:= inv1BcXr (-1); rewrite !scaleN1r opprK. Qed.

End Derivative.


Section FPSComRing.

Variable R : comRingType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).

Lemma mul_series_comm : @commutative {series R} {series R} *%R.
Proof.
move=> s t; apply/seriesP=> i; rewrite coefsM coefsMr.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical series_comRingType :=
  Eval hnf in ComRingType {series R} mul_series_comm.
Canonical fpseries_comRingType :=
  Eval hnf in ComRingType (fpseries R) mul_series_comm.
Canonical series_algType := Eval hnf in CommAlgType R {series R}.
Canonical pfseries_algType :=
  Eval hnf in [algType R of fpseries R for series_algType].

End FPSComRing.


Section FPSUnitRing.

Variable R : unitRingType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).


Definition unit_series : pred {series R} := fun s => s``_0 \in GRing.unit.

(* Noncommutative setting : we define a left and right inverve, getting  *)
(* that they are equal only latter thank to general semigroup theory.    *)
Fixpoint inv_series_rec s bound n :=
  if bound is b.+1 then
    if (n <= b)%N then inv_series_rec s b n
    else - (\sum_(i < n) (inv_series_rec s b i) * s``_(n - i)) * s``_0^-1
  else s``_0^-1.
Definition inv_series s : {series R} :=
  if unit_series s then \series inv_series_rec s i i .X^i else s.

Fixpoint inv_seriesr_rec s bound n :=
  if bound is b.+1 then
    if (n <= b)%N then inv_seriesr_rec s b n
    else - s``_0^-1 * (\sum_(i < n) s``_i.+1 * (inv_seriesr_rec s b (n - i.+1)%N))
  else s``_0^-1.
Definition inv_seriesr s : {series R} :=
  if unit_series s then \series inv_seriesr_rec s i i .X^i else s.

Lemma coefs0_inv_series s : unit_series s -> (inv_series s)``_0 = s``_0^-1.
Proof. by rewrite /inv_series=> ->; rewrite /= coefs_series. Qed.
Lemma coefs0_inv_seriesr s : unit_series s -> (inv_seriesr s)``_0 = s``_0^-1.
Proof. by rewrite /inv_seriesr=> ->; rewrite /= coefs_series. Qed.

Lemma coefsS_inv_series s n :
  unit_series s ->
  (inv_series s)``_n.+1 =
  - (\sum_(i < n.+1) (inv_series s)``_i * s``_(n.+1 - i)) * s``_0^-1.
Proof.
move=> s_unit; rewrite /inv_series s_unit coefs_series /= ltnn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => Hi _.
rewrite coefs_series; congr (_ * _).
move: Hi => /subnKC <-; elim: (n - i)%N => [|{}n IHn]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.
Lemma coefsS_inv_seriesr s n :
  unit_series s ->
  (inv_seriesr s)``_n.+1 =
  - s``_0^-1 * (\sum_(i < n.+1) s``_(i.+1) * (inv_seriesr s)``_(n - i)%N).
Proof.
move=> s_unit; rewrite /inv_seriesr s_unit coefs_series /= ltnn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => Hi _.
rewrite coefs_series; congr (_ * _).
rewrite /bump /= subSS.
move: (n - i)%N (leq_subr i n) {Hi} => {}i Hi.
move: Hi => /subnKC <-; elim: (n - i)%N => [|{}n IHn]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_seriesVr : {in unit_series, left_inverse 1 inv_series *%R}.
Proof.
move=> s s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/seriesP => n; elim: n {1 3 4}n (leqnn n) => [| n IHn] i.
  rewrite leqn0 => /eqP ->; rewrite coefsM big_ord_recr /= big_ord0.
  by rewrite add0r subnn coefs0_inv_series // mulVr // coefsC.
move=> Hi; case: (leqP i n) => [|Hni]; first exact: IHn.
have {Hi Hni i} -> : i = n.+1 by apply anti_leq; rewrite Hi Hni.
rewrite coefs1 /= coefsM big_ord_recr /= subnn coefsS_inv_series //.
by rewrite divrK // subrr.
Qed.

Lemma mul_seriesrVr : {in unit_series, right_inverse 1 inv_seriesr *%R}.
Proof.
move=> s s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/seriesP => n; elim: n {1 3 4}n (leqnn n) => [| n IHn] i.
  rewrite leqn0 => /eqP ->; rewrite coefsM big_ord_recr /= big_ord0.
  by rewrite add0r subnn coefs0_inv_seriesr // mulrV // coefsC.
move=> Hi; case: (leqP i n) => [|Hni]; first exact: IHn.
have {Hi Hni i} -> : i = n.+1 by apply anti_leq; rewrite Hi Hni.
rewrite coefs1 /= coefsM big_ord_recl /= coefsS_inv_seriesr //.
by rewrite mulNr mulrN mulVKr //= addrC subrr.
Qed.

(* General semi-group theory : left inverse = right inverse *)
Lemma unit_seriesE s : unit_series s -> inv_series s = inv_seriesr s.
Proof.
move=> H; have:= erefl (inv_series s * s * inv_seriesr s).
by rewrite -{1}mulrA mul_seriesVr // mul1r mul_seriesrVr // mulr1.
Qed.

Lemma mul_seriesrV : {in unit_series, right_inverse 1 inv_series *%R}.
Proof. by move=> s Hs; rewrite unit_seriesE // mul_seriesrVr. Qed.

Lemma unit_seriesP s t : t * s = 1 /\ s * t = 1 -> unit_series s.
Proof.
move=> [] /(congr1 (coefs 0)); rewrite /= coefs1 /= coefsM => Hl.
move=>    /(congr1 (coefs 0)); rewrite /= coefs1 /= coefsM.
move: Hl; rewrite !big_ord_recr !big_ord0 /= !simp subnn => Hl Hr.
by rewrite /unit_series; apply/unitrP; exists t``_0.
Qed.

Lemma inv_series0id : {in [predC unit_series], inv_series =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_series unfold_in /unit_series => /negbTE ->.
Qed.

Definition series_unitMixin :=
  UnitRingMixin mul_seriesVr mul_seriesrV unit_seriesP inv_series0id.

Canonical series_unitRingType :=
  Eval hnf in UnitRingType {series R} series_unitMixin.
Canonical fpseries_unitRingType :=
  Eval hnf in [unitRingType of fpseries R for series_unitRingType].

Lemma coefsV0 s : unit_series s -> s^-1``_0 = s``_0^-1.
Proof. exact: coefs0_inv_series. Qed.

Lemma series_unitE s : (s \in GRing.unit) = (s``_0 \in GRing.unit).
Proof. by []. Qed.

Lemma seriesC_inv c : c%:S^-1 = (c^-1)%:S.
Proof.
have [/rmorphV-> // | nUc] := boolP (c \in GRing.unit).
by rewrite !invr_out // series_unitE coefsC /= (negbTE nUc).
Qed.

End FPSUnitRing.


Section FPSComUnitRing.

Variable R : comUnitRingType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).

Canonical series_unitAlgType := Eval hnf in [unitAlgType R of {series R}].
Canonical fpseries_unitAlgType := Eval hnf in [unitAlgType R of fpseries R].

Canonical series_comUnitRingType :=
  Eval hnf in [comUnitRingType of {series R}].
Canonical fpseries_comUnitRingType :=
  Eval hnf in [comUnitRingType of fpseries R].

End FPSComUnitRing.


Section FPSIDomain.

Variable R : idomainType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).

Lemma valuatM s1 s2 :
  valuat (s1 * s2) = addbar (valuat s1) (valuat s2).
Proof.
case: (valuatXnP s1)=> [v1 t1 Hv1|]->{s1} /=; last by rewrite !mul0r valuat0.
case: (valuatXnP s2)=> [v2 t2 Hv2|]->{s2} /=; last by rewrite !mulr0 valuat0.
rewrite mulrA (commr_seriesXn v2) mulrA -exprD addnC -mulrA.
apply: valuatXnE; rewrite coefsM big_ord_recr big_ord0 /= add0r subn0.
by rewrite mulf_eq0 negb_or Hv1 Hv2.
Qed.

Lemma valuat_prod (I : Type ) (s : seq I) (P : pred I) (F : I -> {series R}) :
  valuat (\prod_(i <- s | P i) F i) =
  \big[addbar/Nat 0]_(i <- s | P i) valuat (F i).
Proof. exact: (big_morph _ valuatM valuat1). Qed.


Lemma sleadM : {morph (@slead R) : s1 s2 / s1 * s2}.
Proof.
move=> s1 s2; rewrite /slead valuatM.
case: (valuatXnP s1)=> [v1 t1 Hv1|]->{s1} /=; last by rewrite !mul0r.
case: (valuatXnP s2)=> [v2 t2 Hv2->{s2}| _]; last by rewrite !mulr0.
rewrite mulrA (commr_seriesXn v2) mulrA -exprD addnC -mulrA.
by rewrite !coefsXnM !ltnn !subnn coefsM big_ord_recr big_ord0 /= add0r subn0.
Qed.
Lemma slead_prod (I : Type ) (s : seq I) (P : pred I) (F : I -> {series R}) :
  slead (\prod_(i <- s | P i) F i) = \prod_(i <- s | P i) slead (F i).
Proof. exact: (big_morph _ sleadM slead1). Qed.

Fact series_idomainAxiom s t : s * t = 0 -> (s == 0) || (t == 0).
Proof. by move/eqP; rewrite !valuatInfE valuatM addbar_eqI. Qed.

Canonical series_idomainType :=
  Eval hnf in IdomainType {series R} series_idomainAxiom.
Canonical fpseries_idomainType :=
  Eval hnf in [idomainType of fpseries R for series_idomainType].

End FPSIDomain.
Arguments valuatM {R}.
Arguments sleadM {R}.



From mathcomp Require Import finmap.


Section HugeOp.

Variables (R : ringType) (I : choiceType).
Variables (idx : {series R}) (op : Monoid.com_law idx).

Implicit Type F : I -> {series R}.
Implicit Types (a b c x y z : R) (s t r d : {series R}).

Definition n_unit n t := forall s, (op t s)``_n = s``_n.
Definition is_fps_opable F :=
  forall n, exists s : seq I, forall i, i \notin s -> n_unit n (F i).
Lemma fps_opable_spec F :
  is_fps_opable F ->
  forall n : nat, { f : {fset I} | f =i predC (fun i => `[< n_unit n (F i)>]) }.
Proof.
move=> H n; move/(_ n): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq i <- s | ~~ `[< n_unit n (F i)>]]) => i.
rewrite seq_fsetE !inE mem_filter.
by case: (boolP `[< _>]) => //=; apply contraR => /Hs/asboolT.
Qed.
Definition fps_opable F (sm : is_fps_opable F) n :=
  let: exist fs _ := fps_opable_spec sm n in fs.

Lemma fps_opableP F (sm : is_fps_opable F) n i :
  reflect (n_unit n (F i)) (i \notin (fps_opable sm n)).
Proof.
rewrite /fps_opable; apply (iffP negP); case: fps_opable_spec => f Hf.
- by rewrite Hf inE => /negP; rewrite negbK => /asboolW.
- by rewrite Hf inE => H; apply/negP; rewrite negbK; apply asboolT.
Qed.

Definition HugeOp F : {series R} :=
  if pselect (is_fps_opable F) is left Pf
  then \series (\big[op/idx]_(i <- fps_opable Pf n) F i)``_n .X^n
  else idx.

Local Notation "\Op_( i ) F" := (HugeOp (fun i => F)) (at level 0).

(*
Lemma coefsHugeOp F n (f : {fset I}) :
  is_fps_opable F ->
  subpred (predC (mem f)) (fun i => `[< n_unit n (F i)>]) ->
  (\Op_( i ) (F i))``_n = (\big[op/idx]_(i <- f) (F i))``_n.
Proof.
rewrite /HugeOp=> Hop Hsub; case: pselect; last by move=> /(_ Hop).
move=> /= {Hop} Hop; rewrite coefs_series.
transitivity ((\big[op/idx]_(i <- f | i \in fps_opable Hop n) F i)``_n).
rewrite [RHS](bigID [pred i | `[< n_unit n (F i)>]]) /=.
rewrite [X in (_ + X)]big1 ?addr0; last by move=> i; rewrite negbK => /eqP.
rewrite -[RHS]big_filter; apply: perm_big.
apply: (uniq_perm (fset_uniq _) (filter_uniq _ (enum_finpred_uniq _))) => i.
rewrite fps_opableE mem_filter inE enum_finpredE.
 by case: (boolP (_ == 0)) => // /Hsub /= ->.
Qed.
 *)

End HugeOp.

Section Summable.

Variables (R : ringType) (I : choiceType).
Implicit Type F : I -> {series R}.

(* The following definition is here to have something in Prop / bool *)
Definition is_fps_summable F :=
  forall n, exists s : seq I, forall t, (F t)``_n != 0 -> t \in s.
Lemma fps_summable_spec F :
  is_fps_summable F ->
  forall n : nat, { f : {fset I} | f =i [pred t : I | (F t)``_n != 0] }.
Proof.
move=> H n; move/(_ n): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq t <- s | (F t)``_n != 0]) => i /=.
rewrite seq_fsetE !inE mem_filter.
by case: eqP => [|/eqP/Hs ->].
Qed.
Definition fps_summable F (sm : is_fps_summable F) n :=
  let: exist fs _ := fps_summable_spec sm n in fs.

Lemma fps_summableE F (sm : is_fps_summable F) :
  forall n, (fps_summable sm n) =i [pred t : I | (F t)``_n != 0].
Proof. by rewrite /fps_summable; move=> n; case: fps_summable_spec. Qed.

Definition HugeSum F : {series R} :=
  if pselect (is_fps_summable F) is left Pf
  then \series \sum_(t <- fps_summable Pf n) (F t)``_n .X^n
  else 0.

Notation "\Sum_( i : t ) F" := (HugeSum (fun i : t => F)).

Lemma coefsHugeSum F n (fpI : finpredType I) (p : fpI) :
  is_fps_summable F -> subpred [pred t : I | (F t)``_n != 0] (mem p) ->
  (\Sum_( i : I ) F i)``_n = \sum_(i <- enum_finpred p) (F i)``_n.
Proof.
rewrite /HugeSum=> Hsum Hsub; case: pselect; last by move=> /(_ Hsum).
move=> /= {}Hsum; rewrite coefs_series.
rewrite [RHS](bigID [pred t | (F t)``_n != 0]) /=.
rewrite [X in (_ + X)]big1 ?addr0; last by move=> i; rewrite negbK => /eqP.
rewrite -[RHS]big_filter; apply: perm_big.
apply: (uniq_perm (fset_uniq _) (filter_uniq _ (enum_finpred_uniq _))) => i.
rewrite fps_summableE mem_filter inE enum_finpredE.
 by case: (boolP (_ == 0)) => // /Hsub /= ->.
Qed.

Lemma coefsHugeSum_fset F n (S : {fset I}) :
  is_fps_summable F -> subpred [pred t : I | (F t)``_n != 0] (mem S) ->
  (\Sum_( i : I ) F i)``_n = \sum_(i <- S) (F i)``_n.
Proof. exact: coefsHugeSum. Qed.

Lemma coefsHugeSum_seq F n (S : seq I) :
  is_fps_summable F -> subpred [pred t : I | (F t)``_n != 0] (mem S) ->
  (\Sum_( i : I ) F i)``_n = \sum_(i <- undup S) (F i)``_n.
Proof. by move/coefsHugeSum=> H{}/H ->; rewrite /enum_finpred. Qed.

End Summable.
Notation "\Sum_( i : t ) F" := (HugeSum (fun i : t => F)).
Notation "\Sum_( i ) F" := (HugeSum (fun i : nat => F)).



Section Tests.

Variable R : ringType.

Lemma Xn_summable : is_fps_summable (fun i : nat => ''X^i : {series R}).
Proof.
move=> m /=; exists [:: m] => n.
rewrite coefsXn inE (eq_sym m n); case (boolP (n == m)) => //=.
by rewrite eqxx.
Qed.

Lemma εὕρηκα : \Sum_(n) ''X^n = \series 1 .X^n :> {series R}.
Proof.
apply/seriesP => i; rewrite (coefsHugeSum_seq Xn_summable (S := [:: i])).
  by rewrite /= big_seq1 coefsXn coefs_series eqxx.
move=> n; rewrite !inE coefsXn (eq_sym i).
by case: (n == i); rewrite ?eqxx ?oner_eq0.
Qed.

Lemma geom_seriesM : (\Sum_(n) ''X^n) * (1 - ''X) = 1 :> {series R}.
Proof. by rewrite εὕρηκα inv1BXr. Qed.

End Tests.

Lemma geom_series (R : unitRingType) :
  (1 - ''X)^-1 = \Sum_(n) ''X^n :> {series R}.
Proof.
have mdu : ((1 - ''X) : {series R}) \is a GRing.unit.
  by rewrite !unfold_in /= /unit_series coefsB coefs1 coefsX /= subr0 unitr1.
by apply (mulIr mdu); rewrite geom_seriesM mulVr.
Qed.

Section NatSummable.

Variable R : ringType.
Implicit Type F : nat -> {series R}.

Lemma summable_valuat F :
  (forall v : nat, exists n0,
        forall n, (n0 <= n)%N -> (valuat (F n) >= Nat v)%O) ->
  is_fps_summable F.
Proof.
move=> H v /=; move/(_ v.+1): H => [n0 Hn0].
exists (iota 0 n0) => n; rewrite mem_iota /= add0n.
apply contra_neqT; rewrite -leqNgt => {}/Hn0.
by have:= ltnSn v; rewrite -ltEnatbar => /lt_le_trans H{}/H/coefs_le_valuat.
Qed.

Lemma summable_valuat_lek F k :
  (forall n, (Nat (n - k) <= valuat (F n))%O) -> is_fps_summable F.
Proof.
move=> H; apply summable_valuat => v.
exists (v + k)%N => n /(leq_sub2r k).
by rewrite addnK -leEnatbar => /le_trans/(_ (H _)).
Qed.

Lemma summable_valuat_le F :
  (forall n, (Nat n <= valuat (F n))%O) -> is_fps_summable F.
Proof.
move=> H; apply: (summable_valuat_lek (k := 0)) => n.
by rewrite subn0.
Qed.

Lemma coefsHugeSumE F d n0 S :
  (forall n, (n >= n0)%N -> (\sum_(i < n) F i)``_d = S) ->
  is_fps_summable F ->
  (\Sum_(i) F i)``_d = \sum_(i < n0) (F i)``_d.
Proof.
move=> Heq /(coefsHugeSum_seq (S := iota 0 n0)) ->.
  by rewrite (undup_id (iota_uniq _ _)) -{1}(subn0 n0) big_mkord.
move=> /= n; rewrite mem_iota /= add0n.
rewrite ltnNge; apply contra_neqN => n0len.
have := Heq _ n0len.
rewrite -(Heq n.+1 (leq_trans n0len _)) // => /eqP.
by rewrite big_ord_recr /= coefsD addrC -subr_eq subrr => /eqP <-.
Qed.

End NatSummable.



(*
Definition is_fps_summable F :=
  forall n, exists s : seq T, forall t, (F t)``_n != 0 -> t \in s.
Definition fps_summable F :=     (* summability In Type *)
  forall n, is_finite [pred t : T | (F t)``_n != 0].


Lemma is_fps_summableP F : is_fps_summable F -> fps_summable F.
Proof.
move=> H n; move/(_ n): H => /cid [s Hs].
apply: (IsFinite (undup_uniq [seq t <- s | (F t)``_n != 0])) => t.
rewrite mem_undup mem_filter /=.
by case: eqP => [|/eqP/Hs ->].
Qed.

Definition HugeSum F : {series R} :=
  if pselect (is_fps_summable F) is left Pf
  then \series \sum_(t <- is_fps_summableP Pf n) (F t)``_n .X^n
  else 0.

End Summable.
Notation "\Sum_( i : t ) F" := (HugeSum (fun i : t => F)).
Notation "\Sum_( i ) F" := (HugeSum (fun i : nat => F)).

Section Tests.

Variable R : ringType.

Lemma Xn_summable : is_fps_summable (fun i : nat => ''X^i : {series R}).
Proof.
move=> m /=; exists [:: m] => n.
rewrite coefsXn inE (eq_sym m n); case (boolP (n == m)) => //=.
by rewrite eqxx.
Qed.

Lemma εὕρηκα : \Sum_(n) ''X^n = \series 1 .X^n :> {series R}.
Proof.
rewrite /HugeSum; apply/seriesP => n.
case pselect => [Hl | /(_ Xn_summable)//].
rewrite !coefs_series.
case: is_fps_summableP=> /= s s_uniq Hs.
rewrite (bigD1_seq n) ?{}s_uniq //= ?Hs coefsXn eqxx //= ?oner_neq0 //.
rewrite big1 ?addr0 // => i /negbTE.
by rewrite coefsXn eq_sym => ->.
Qed.

End Tests.
*)


