From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.



Reserved Notation "{ 'series' T }" (at level 0, format "{ 'series'  T }").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\series_ ( i ) E"
  (at level 36, E at level 36, i at level 50,
   format "\series_ ( i )  E").
Reserved Notation "a ^`` ()" (at level 8, format "a ^`` ()").
Reserved Notation "s ``_ i" (at level 3, i at level 2, left associativity,
                            format "s ``_ i").

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
Notation coefps i := (coefps_head tt i).
Notation "s ``_ i" := (coef_series s i).


Section SymPolyRingType.

Variable R : ringType.

Implicit Types (a b c x y z : R) (p q r d : {series R}).

Lemma coefpsE i p : coefps i p = p``_i.
Proof. by []. Qed.

Local Notation "\series_ ( i ) E" := (@FPSeries R (fun i : nat => E)).

Lemma coefs_series E j : (\series_ ( i ) E i)``_j = E j.
Proof. by rewrite unlock. Qed.

Definition seriesC c : {series R} := \series_(i) if i is _.+1 then 0 else c.
Local Notation "c %:S" := (seriesC c).

Lemma coefsC c i : c%:S``_i = if i == 0%N then c else 0.
Proof. by rewrite coefs_series; case: i. Qed.

Lemma coefsC0 i : 0%:S``_i = 0.
Proof. by rewrite coefs_series; case: i. Qed.

Lemma seriesCK : cancel seriesC (coefps 0).
Proof. by move=> c; rewrite /= coefsC. Qed.

Lemma seriesC_inj : injective seriesC.
Proof. by move=> c1 c2 eqc12; have:= coefsC c2 0; rewrite -eqc12 coefsC. Qed.

Lemma seriesfunP p q : (seriesfun p) =1 (seriesfun q) <-> p = q.
Proof. by rewrite -funeqE; split=> [eq_pq | -> //]; apply: seriesfun_inj. Qed.

Lemma seriesP p q : (forall n, p``_n = q``_n) <-> (p = q).
Proof.
rewrite unlock /= -/(seriesfun p =1 seriesfun q) -funeqE.
by split => [/seriesfun_inj | -> //].
Qed.

Lemma seriesfunK p : FPSeries (seriesfun p) = p.
Proof. exact: seriesfun_inj. Qed.

(* Build a series from a function: Is the following useful ?
Definition series_expanded_def E := @FPSeries R E.
Fact series_key : unit. Proof. by []. Qed.
Definition series := locked_with series_key series_expanded_def.
Canonical series_unlockable := [unlockable fun series].
Local Notation "\series_ ( i ) E" := (series (fun i : nat => E)). *)


(* Zmodule structure for Formal power series *)
Definition add_series_def p q := \series_(i) (p``_i + q``_i).
Fact add_series_key : unit. Proof. by []. Qed.
Definition add_series := locked_with add_series_key add_series_def.
Canonical add_series_unlockable := [unlockable fun add_series].

Definition opp_series_def p := \series_(i) - p``_i.
Fact opp_series_key : unit. Proof. by []. Qed.
Definition opp_series := locked_with opp_series_key opp_series_def.
Canonical opp_series_unlockable := [unlockable fun opp_series].

Fact coefs_add_series p q i : (add_series p q)``_i = p``_i + q``_i.
Proof. by rewrite [add_series]unlock coefs_series. Qed.

Fact coefs_opp_series p i : (opp_series p)``_i = - (p``_i).
Proof. by rewrite [opp_series]unlock coefs_series. Qed.

Fact add_seriesA : associative add_series.
Proof. by move=> p q r; apply/seriesP=> i; rewrite !coefs_add_series addrA. Qed.

Fact add_seriesC : commutative add_series.
Proof. by move=> p q; apply/seriesP=> i; rewrite !coefs_add_series addrC. Qed.

Fact add_series0 : left_id 0%:S add_series.
Proof.
by move=> p; apply/seriesP=>[i]; rewrite coefs_add_series coefsC0 add0r.
Qed.

Fact add_seriesN : left_inverse 0%:S opp_series add_series.
Proof.
move=> p; apply/seriesP=> i.
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

Lemma seriesC_eq0 (c : R) : (c%:S == 0) = (c == 0).
Proof. by apply/eqP/eqP => [/seriesfunP/(_ 0%N) | ->]. Qed.

Lemma coefsD p q i : (p + q)``_i = p``_i + q``_i.
Proof. exact: coefs_add_series. Qed.

Lemma coefsN p i : (- p)``_i = - (p``_i).
Proof. exact: coefs_opp_series. Qed.

Lemma coefsB p q i : (p - q)``_i = p``_i - q``_i.
Proof. by rewrite coefsD coefsN. Qed.

Canonical coefps_additive i :=
  Additive ((fun p => (coefsB p)^~ i) : additive (coefps i)).

Lemma coefsMn p n i : (p *+ n)``_i = (p``_i) *+ n.
Proof.  exact: (raddfMn (coefps_additive i)). Qed.

Lemma coefsMNn p n i : (p *- n)``_i = (p``_i) *- n.
Proof. by rewrite coefsN coefsMn. Qed.

Lemma coefs_sum I (r : seq I) (P : pred I) (F : I -> {series R}) k :
  (\sum_(i <- r | P i) F i)``_k = \sum_(i <- r | P i) (F i)``_k.
Proof. exact: (raddf_sum (coefps_additive k)). Qed.

Lemma seriesC_add : {morph seriesC : a b / a + b}.
Proof.
by move=> a b; apply/seriesP=> [[|i]]; rewrite coefsD !coefsC ?addr0.
Qed.

Lemma seriesC_opp : {morph seriesC : c / - c}.
Proof.
by move=> c; apply/seriesP=> [[|i]]; rewrite coefsN !coefsC ?oppr0.
Qed.

Lemma seriesC_sub : {morph seriesC : a b / a - b}.
Proof. by move=> a b; rewrite seriesC_add seriesC_opp. Qed.

Canonical seriesC_additive := Additive seriesC_sub.

Lemma seriesC_muln n : {morph seriesC : c / c *+ n}.
Proof. exact: raddfMn. Qed.


(* Formal power series ring structure. *)

Definition mul_series_def p q :=
  \series_(i) (\sum_(j < i.+1) p``_j * q``_(i - j)).
Fact mul_series_key : unit. Proof. by []. Qed.
Definition mul_series := locked_with mul_series_key mul_series_def.
Canonical mul_series_unlockable := [unlockable fun mul_series].

Fact coefs_mul_series p q i :
  (mul_series p q)``_i = \sum_(j < i.+1) p``_j * q``_(i - j).
Proof. by rewrite !unlock. Qed.

Fact coefs_mul_series_rev p q i :
  (mul_series p q)``_i = \sum_(j < i.+1) p``_(i - j) * q``_j.
Proof.
rewrite coefs_mul_series (reindex_inj rev_ord_inj) /=.
by apply: eq_bigr => j _; rewrite (sub_ordK j).
Qed.

Fact mul_seriesA : associative mul_series.
Proof.
move=> p q r; apply/seriesP=> i; rewrite coefs_mul_series coefs_mul_series_rev.
pose coef3 j k := p``_j * (q``_(i - j - k) * r``_k).
transitivity (\sum_(j < i.+1) \sum_(k < i.+1 | (k <= i - j)%N) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coefs_mul_series_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep predT) //=; apply: eq_bigr => k _.
transitivity (\sum_(j < i.+1 | (j <= i - k)%N) coef3 j k).
  apply: eq_bigl => j; rewrite -ltnS -(ltnS j) -!subSn ?leq_ord //.
  by rewrite -subn_gt0 -(subn_gt0 j) -!subnDA addnC.
rewrite (big_ord_narrow_leq (leq_subr _ _)) coefs_mul_series big_distrl /=.
by apply: eq_bigr => j _; rewrite /coef3 -!subnDA addnC mulrA.
Qed.

Fact mul_1series : left_id 1%:S mul_series.
Proof.
move=> p; apply/seriesP => i; rewrite coefs_mul_series big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefsC /= !simp.
Qed.

Fact mul_series1 : right_id 1%:S mul_series.
Proof.
move=> p; apply/seriesP => i; rewrite coefs_mul_series_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefsC !simp.
Qed.

Fact mul_seriesDl : left_distributive mul_series +%R.
Proof.
move=> p q r; apply/seriesP=> i; rewrite coefsD !coefs_mul_series -big_split.
by apply: eq_bigr => j _; rewrite coefsD mulrDl.
Qed.

Fact mul_seriesDr : right_distributive mul_series +%R.
Proof.
move=> p q r; apply/seriesP=> i; rewrite coefsD !coefs_mul_series -big_split.
by apply: eq_bigr => j _; rewrite coefsD mulrDr.
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

Lemma coefs1 i : (1 : {series R})``_i = (i == 0%N)%:R.
Proof. by rewrite unlock; case: i. Qed.

Lemma coefsM p q i : (p * q)``_i = \sum_(j < i.+1) p``_j * q``_(i - j).
Proof. exact: coefs_mul_series. Qed.

Lemma coefsMr p q i : (p * q)``_i = \sum_(j < i.+1) p``_(i - j) * q``_j.
Proof. exact: coefs_mul_series_rev. Qed.

Lemma coefsCM c p i : (c%:S * p)``_i = c * (p``_i).
Proof.
rewrite coefsM big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefsC !simp.
Qed.

Lemma coefsMC c p i : (p * c%:S)``_i = p``_i * c.
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

Lemma seriesC_exp n : {morph seriesC : c / c ^+ n}.
Proof. exact: rmorphX. Qed.

Fact coefps0_multiplicative : multiplicative (coefps 0 : {series R} -> R).
Proof.
split=> [p q|]; last by rewrite seriesCK.
by rewrite !coefpsE coefsM big_ord_recl big_ord0 addr0.
Qed.

Canonical coefps0_rmorphism := AddRMorphism coefps0_multiplicative.


(* Algebra structure of formal power series. *)
Definition scale_series_def a (p : {series R}) := \series_(i) (a * p``_i).
Fact scale_series_key : unit. Proof. by []. Qed.
Definition scale_series := locked_with scale_series_key scale_series_def.
Canonical scale_series_unlockable := [unlockable fun scale_series].

Fact scale_seriesE a p : scale_series a p = a%:S * p.
Proof.
by apply/seriesP=> n; rewrite [scale_series]unlock coefs_series coefsCM.
Qed.

Fact scale_seriesA a b p :
  scale_series a (scale_series b p) = scale_series (a * b) p.
Proof. by rewrite !scale_seriesE mulrA seriesC_mul. Qed.

Fact scale_1series : left_id 1 scale_series.
Proof. by move=> p; rewrite scale_seriesE mul1r. Qed.

Fact scale_seriesDr a : {morph scale_series a : p q / p + q}.
Proof. by move=> p q; rewrite !scale_seriesE mulrDr. Qed.

Fact scale_seriesDl p : {morph scale_series^~ p : a b / a + b}.
Proof. by move=> a b /=; rewrite !scale_seriesE raddfD mulrDl. Qed.

Fact scale_seriesAl a p q : scale_series a (p * q) = scale_series a p * q.
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


Lemma mul_seriesC a p : a%:S * p = a *: p.
Proof. by rewrite -scale_seriesE. Qed.

Lemma alg_seriesC a : a%:A = a%:S :> {series R}.
Proof. by rewrite -mul_seriesC mulr1. Qed.

Lemma coefsZ a p i : (a *: p)``_i = a * p``_i.
Proof.
by rewrite -[*:%R]/scale_series [scale_series]unlock coefs_series.
Qed.

Canonical coefps_linear i : {scalar {series R}} :=
  AddLinear ((fun a => (coefsZ a) ^~ i) : scalable_for *%R (coefps i)).
Canonical coefp0_lrmorphism := [lrmorphism of coefps 0].


(* The indeterminate, at last! *)
Definition seriesX_def := \series_(i) if i == 1%N then 1 else 0 : R.
Fact seriesX_key : unit. Proof. by []. Qed.
Definition seriesX : {series R} := locked_with seriesX_key seriesX_def.
Canonical seriesX_unlockable := [unlockable of seriesX].
Local Notation "'Xs" := seriesX.

Lemma seriesfunX :
  seriesfun 'Xs = (fun i => if i == 1%N then 1 else 0 : R).
Proof. by rewrite unlock. Qed.

Lemma seriesX_eq0 : ('Xs == 0) = false.
Proof.
apply/negP=> /eqP; apply/seriesfunP => /(_ 1%N)/eqP.
by rewrite seriesfunX /= oner_eq0.
Qed.

Lemma coefsX i : 'Xs``_i = (i == 1%N)%:R.
Proof. by case: i => [|[|i]]; rewrite [seriesX]unlock /= coefs_series. Qed.

Lemma commr_seriesX p : GRing.comm p 'Xs.
Proof.
apply/seriesP=> i; rewrite coefsMr coefsM.
by apply: eq_bigr => j _; rewrite coefsX commr_nat.
Qed.

Lemma coefsMX p i : (p * 'Xs)``_i = (if (i == 0)%N then 0 else p``_i.-1).
Proof.
rewrite coefsMr big_ord_recl coefsX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl  /= !coefsX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite coefsX /= !simp.
Qed.

Lemma coefXM p i : ('Xs * p)``_i = (if (i == 0)%N then 0 else p``_i.-1).
Proof. by rewrite -commr_seriesX coefsMX. Qed.

Lemma lreg_seriesZ_eq0 c p : GRing.lreg c -> (c *: p == 0) = (p == 0).
Proof.
move=> creg; apply/eqP/eqP => [|->]; last by rewrite scaler0.
rewrite -!seriesP => H i.
by have/eqP := H i; rewrite coefs0 coefsZ mulrI_eq0 // => /eqP.
Qed.

Lemma rreg_seriesMC_eq0 c p : GRing.rreg c -> (p * c%:S == 0) = (p == 0).
Proof.
move=> creg; apply/eqP/eqP => [|->]; last by rewrite mul0r.
rewrite -!seriesP => H i.
by have/eqP := H i; rewrite coefs0 coefsMC mulIr_eq0 // => /eqP.
Qed.


(* Lifting a ring predicate to series. *)

Implicit Type S : {pred R}.

Definition seriesOver S :=
  [qualify a p : {series R} | `[forall n, `[< p``_n \in S >] ] ].

Fact seriesOver_key S : pred_key (seriesOver S). Proof. by []. Qed.
Canonical seriesOver_keyed S := KeyedQualifier (seriesOver_key S).

Lemma seriesOverS (S1 S2 : {pred R}) :
  {subset S1 <= S2} -> {subset seriesOver S1 <= seriesOver S2}.
Proof.
move =>sS12 p /forallp_asboolP S1p.
by apply/forallp_asboolP => i; apply: sS12.
Qed.

Section SeriesOverAdd.

Variables (S : {pred R}) (addS : addrPred S) (kS : keyed_pred addS).

Lemma seriesOver0 : 0 \is a seriesOver kS.
Proof. by apply/forallp_asboolP => n; rewrite coefs0 rpred0. Qed.

Lemma seriesOverP {p} : reflect (forall i, p``_i \in kS) (p \in seriesOver kS).
Proof. exact: (iffP forallp_asboolP). Qed.

Lemma seriesOverC c : (c%:S \in seriesOver kS) = (c \in kS).
Proof.
by apply/seriesOverP/idP => [/(_ 0%N)| cS [|i]]; rewrite coefsC //= rpred0.
Qed.

Fact seriesOver_addr_closed : addr_closed (seriesOver kS).
Proof.
split=> [|p q Sp Sq]; first exact: seriesOver0.
by apply/seriesOverP=> i; rewrite coefsD rpredD ?(seriesOverP _).
Qed.
Canonical seriesOver_addrPred := AddrPred seriesOver_addr_closed.

End SeriesOverAdd.


Fact seriesOverNr S (addS : zmodPred S) (kS : keyed_pred addS) :
  oppr_closed (seriesOver kS).
Proof.
by move=> p /seriesOverP Sp; apply/seriesOverP=> i; rewrite coefsN rpredN.
Qed.
Canonical seriesOver_opprPred S addS kS := OpprPred (@seriesOverNr S addS kS).
Canonical seriesOver_zmodPred S addS kS := ZmodPred (@seriesOverNr S addS kS).

Section SeriesOverSemiring.

Variables (S : {pred R}) (ringS : semiringPred S) (kS : keyed_pred ringS).

Fact seriesOver_mulr_closed : mulr_closed (seriesOver kS).
Proof.
split=> [|p q /seriesOverP Sp /seriesOverP Sq].
- by rewrite seriesOverC rpred1.
- by apply/seriesOverP=> i; rewrite coefsM rpred_sum // => j _; apply: rpredM.
Qed.
Canonical seriesOver_mulrPred := MulrPred seriesOver_mulr_closed.
Canonical seriesOver_semiringPred := SemiringPred seriesOver_mulr_closed.

Lemma seriesOverZ : {in kS & seriesOver kS, forall c p, c *: p \is a seriesOver kS}.
Proof.
by move=> c p Sc /seriesOverP Sp; apply/seriesOverP=> i; rewrite coefsZ rpredM ?Sp.
Qed.

Lemma seriesOverX : 'Xs \in seriesOver kS.
Proof.
by apply/seriesOverP=> [] [|[|i]]; rewrite coefsX //= ?rpred0 ?rpred1.
Qed.

End SeriesOverSemiring.

Section SeriesOverRing.

Variables (S : {pred R}) (ringS : subringPred S) (kS : keyed_pred ringS).
Canonical seriesOver_smulrPred := SmulrPred (seriesOver_mulr_closed kS).
Canonical seriesOver_subringPred := SubringPred (seriesOver_mulr_closed kS).

End SeriesOverRing.


(* Single derivative. *)

Definition derivs p := \series_(i) (p``_i.+1 *+ i.+1).

Local Notation "a ^`` ()" := (derivs a).

Lemma coefs_deriv p i : p^``()``_i = p``_i.+1 *+ i.+1.
Proof. by rewrite coefs_series. Qed.

Lemma seriesOver_deriv S (ringS : semiringPred S) (kS : keyed_pred ringS) :
  {in seriesOver kS, forall p, p^``() \is a seriesOver kS}.
Proof.
by move=> p /seriesOverP Kp; apply/seriesOverP=> i; rewrite coefs_deriv rpredMn ?Kp.
Qed.

Lemma derivC c : c%:S^``() = 0.
Proof. by apply/seriesP=> i; rewrite coefs_deriv coefs0 coefsC mul0rn. Qed.

Lemma derivX : 'Xs^``() = 1.
Proof. by apply/seriesP=> [[|i]]; rewrite coefs_deriv coefs1 coefsX ?mul0rn. Qed.
