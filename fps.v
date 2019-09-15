From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.


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

Reserved Notation "a ^`` ()" (at level 8, format "a ^`` ()").
Reserved Notation "s ``_ i" (at level 3, i at level 2, left associativity,
                            format "s ``_ i").





(** Clone of option nat to avoid the very confusing chain of coercions *)
(**   option -> bool -> nat                                            *)

Section NatBar.

Open Scope order_scope.


Inductive natbar : Set :=  Nat of nat | Inf.
Definition opt_natbar (v : natbar) : option nat :=
  if v is Nat n then Some n else None.
Definition natbar_opt (v : option nat) : natbar :=
  if v is Some n then Nat n else Inf.

Lemma opt_natbarK : cancel opt_natbar natbar_opt.
Proof. by case. Qed.
Lemma natbar_optK : cancel natbar_opt opt_natbar.
Proof. by case. Qed.
Definition natbar_eqMixin := CanEqMixin opt_natbarK.
Canonical natbar_eqType := Eval hnf in EqType natbar natbar_eqMixin.
Definition natbar_choiceMixin := CanChoiceMixin opt_natbarK.
Canonical natbar_choiceType := Eval hnf in ChoiceType natbar natbar_choiceMixin.
Definition natbar_countMixin := CanCountMixin opt_natbarK.
Canonical natbar_countType := Eval hnf in CountType natbar natbar_countMixin.

Implicit Type (m n o p : nat).
Implicit Type (u v w x y : natbar).

Lemma Nat_inj : injective Nat. Proof. by move=> m n []. Qed.
Lemma Nat_eqE m n : (Nat m == Nat n) = (m == n).
Proof. by apply/eqP/eqP => [/Nat_inj|<-]. Qed.

Definition addbar u v : natbar :=
  match u, v with
  | Nat m, Nat n => Nat (m + n)
  | _, _ => Inf
  end.

Lemma add0bar : left_id  (Nat 0) addbar. Proof. by case. Qed.
Lemma addbar0 : right_id (Nat 0) addbar.
Proof. by case=> //= n; rewrite addn0. Qed.

Lemma addIbar : left_zero  Inf addbar. Proof. by case. Qed.
Lemma addbarI : right_zero Inf addbar. Proof. by case. Qed.

Lemma addbarCA : left_commutative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnCA. Qed.

Lemma addbarC : commutative addbar.
Proof. by case=> [m|] [n|] //=; rewrite addnC. Qed.

Lemma addbarA : associative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnA. Qed.

Lemma addbarAC : right_commutative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnAC. Qed.

Lemma addbarACA : interchange addbar addbar.
Proof. by case=> [m|] [n|] [p|] [q|] //=; rewrite addnACA. Qed.

Lemma addbar_eq0 u v : (addbar u v == Nat 0) = (u == Nat 0) && (v == Nat 0).
Proof.
by case: u v => [m|] [n|] //=; rewrite !Nat_eqE /= ?addn_eq0 ?andbF.
Qed.

Lemma addbar_eqI u v : (addbar u v == Inf) = (u == Inf) || (v == Inf).
Proof. by case: u v => [m|] [n|]. Qed.

Canonical natbar_monoid := Monoid.Law addbarA add0bar addbar0.
Canonical natbar_comoid := Monoid.ComLaw addbarC.


(** Valuation ordering *)
Definition lebar u v :=
  match u, v with
  | _, Inf => true
  | Nat m, Nat n => m <= n
  | _, _ => false
  end.
Definition ltbar u v := (u != v) && (lebar u v).
Definition lebar_display : unit. Proof. exact: tt. Qed.

Lemma ltbar_def u v : (ltbar u v) = (u != v) && (lebar u v).
Proof. by []. Qed.

Lemma lebarbar : reflexive lebar. Proof. by case => /=. Qed.
Lemma lebar_trans : transitive lebar.
Proof. by case=> [m|] [n|] [p|] //=; apply leq_trans. Qed.
Lemma lebar_anti : antisymmetric lebar.
Proof. by case=> [m|] [n|] //=; rewrite -eqn_leq => /eqP ->. Qed.

Definition natbar_POrderMixin :=
  POrderMixin ltbar_def lebarbar lebar_anti lebar_trans.
Canonical natbar_POrderType  :=
  POrderType lebar_display natbar natbar_POrderMixin.

Lemma leEnatbar (n m : nat) : (Nat n <= Nat m) = (n <= m)%N.
Proof. by []. Qed.

Lemma ltEnatbar (n m : nat) : (Nat n < Nat m) = (n < m)%N.
Proof. by rewrite lt_neqAle leEnatbar Nat_eqE ltn_neqAle. Qed.

Lemma lebar_total : total lebar.
Proof. by case=> [m|] [n|] //=; exact: leq_total. Qed.

Definition natbar_LatticeMixin := Order.TotalLattice.Mixin lebar_total.
Canonical natbar_LatticeType := LatticeType natbar natbar_LatticeMixin.
Canonical natbar_OrderType := OrderType natbar lebar_total.

Lemma le0bar v : Nat 0 <= v. Proof. by case: v. Qed.

Definition natbar_BLatticeMixin := BLatticeMixin le0bar.
Canonical natbar_BLatticeType := BLatticeType natbar natbar_BLatticeMixin.

Lemma lebarI v : v <= Inf. Proof. by case v. Qed.

Definition natbar_TBLatticeMixin := TBLatticeMixin lebarI.
Canonical natbar_TBLatticeType := TBLatticeType natbar natbar_TBLatticeMixin.

Lemma ltbar0Sn n : 0 < Nat n.+1.       Proof. by []. Qed.
Lemma ltbarS n : Nat n < Nat n.+1.     Proof. by rewrite ltEnatbar. Qed.
Lemma lebarS n : Nat n <= Nat n.+1.    Proof. by rewrite leEnatbar. Qed.
Hint Resolve lebarS : core.
Lemma ltIbar v : Inf < v = false.      Proof. exact/le_gtF/lex1. Qed.
Lemma leInatbar n : Inf <= Nat n = false.
Proof. by []. Qed.

Lemma minbarE : {morph Nat : m n / minn m n >-> meet m n}.
Proof.
move=> m n; case: (leqP m n) => [mlen | /ltnW nlem].
- by rewrite (minn_idPl mlen); move: mlen; rewrite -leEnatbar => /meet_idPl.
- by rewrite (minn_idPr nlem); move: nlem; rewrite -leEnatbar => /meet_idPr.
Qed.

Lemma maxbarE : {morph Nat : m n / maxn m n >-> join m n}.
Proof.
move=> m n; case: (leqP m n) => [mlen | /ltnW nlem].
- by rewrite (maxn_idPr mlen); move: mlen; rewrite -leEnatbar => /join_idPl.
- by rewrite (maxn_idPl nlem); move: nlem; rewrite -leEnatbar => /join_idPr.
Qed.

End NatBar.


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

Lemma seriesC_eq0 (c : R) : (c%:S == 0) = (c == 0).
Proof. by apply/eqP/eqP => [/seriesfunP/(_ 0%N) | ->]. Qed.

Lemma coefsD s t i : (s + t)``_i = s``_i + t``_i.
Proof. exact: coefs_add_series. Qed.

Lemma coefsN s i : (- s)``_i = - (s``_i).
Proof. exact: coefs_opp_series. Qed.

Lemma coefsB s t i : (s - t)``_i = s``_i - t``_i.
Proof. by rewrite coefsD coefsN. Qed.

Canonical coefps_additive i :=
  Additive ((fun s => (coefsB s)^~ i) : additive (coefs i)).

Lemma coefsMn s n i : (s *+ n)``_i = (s``_i) *+ n.
Proof.  exact: (raddfMn (coefps_additive i)). Qed.

Lemma coefsMNn s n i : (s *- n)``_i = (s``_i) *- n.
Proof. by rewrite coefsN coefsMn. Qed.

Lemma coefs_sum I (r : seq I) (s : pred I) (F : I -> {series R}) k :
  (\sum_(i <- r | s i) F i)``_k = \sum_(i <- r | s i) (F i)``_k.
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

Fact series_poly_is_additive : additive series_poly.
Proof.
move=> p q; apply/seriesP => n.
by rewrite coefsB !coefs_series coefB.
Qed.
Canonical series_poly_additive := Additive series_poly_is_additive.

Fact poly_series_is_additive d : additive (poly_series d).
Proof.
move=> p q; apply/polyP => n.
by rewrite coefB !coefs_poly_series; case: ltnP => _; rewrite ?subr0 ?coefsB.
Qed.
Canonical poly_series_additive d := Additive (poly_series_is_additive d).



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

Lemma seriesC_exp n : {morph seriesC : c / c ^+ n}.
Proof. exact: rmorphX. Qed.

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

Lemma series_polyD p q : SP (p + q) = SP p + SP q.
Proof. exact: linearD. Qed.

Lemma series_polyN p : SP (- p) = - SP p.
Proof. exact: linearN. Qed.

Lemma series_polyB p q : SP (p - q) = SP p - SP q.
Proof. exact: linearB. Qed.

Lemma series_polyMn p n : SP (p *+ n) = (SP p) *+ n.
Proof. exact: raddfMn. Qed.

Lemma series_polyMNn p n : SP (p *- n) = (SP p) *- n.
Proof. exact: raddfMNn. Qed.

Lemma series_poly_sum I (r : seq I) (s : pred I) (F : I -> {poly R}) :
  SP (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) SP (F i).
Proof. exact: raddf_sum. Qed.

Fact poly_series_is_linear d : linear (poly_series d).
Proof.
move=> i s t; apply/polyP => n.
rewrite coefD coefZ !coefs_poly_series.
by case: ltnP => _; rewrite ?mulr0 ?addr0 // coefsD coefsZ.
Qed.
Canonical poly_series_linear d := Linear (poly_series_is_linear d).

Lemma poly_seriesD d s t : PS d (s + t) = PS d s + PS d t.
Proof. exact: linearD. Qed.

Lemma poly_seriesN d s : PS d (- s) = - PS d s.
Proof. exact: linearN. Qed.

Lemma poly_seriesB d s t : PS d (s - t) = PS d s - PS d t.
Proof. exact: linearB. Qed.

Lemma poly_seriesMn d s n : PS d (s *+ n) = (PS d s) *+ n.
Proof. exact: raddfMn. Qed.

Lemma poly_seriesfMNn d s n : PS d (s *- n) = (PS d s) *- n.
Proof. exact: raddfMNn. Qed.

Lemma poly_series_sum d I (r : seq I) (s : pred I) (F : I -> {series R}) :
  PS d (\sum_(i <- r | s i) F i) = \sum_(i <- r | s i) PS d (F i).
Proof. exact: raddf_sum. Qed.


(* The indeterminate, at last! *)
Definition seriesX_def := \series if i == 1%N then 1 else 0 : R .X^i.
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

Lemma commr_seriesX s : GRing.comm s 'Xs.
Proof.
apply/seriesP=> i; rewrite coefsMr coefsM.
by apply: eq_bigr => j _; rewrite coefsX commr_nat.
Qed.

Lemma coefsMX s i : (s * 'Xs)``_i = (if (i == 0)%N then 0 else s``_i.-1).
Proof.
rewrite coefsMr big_ord_recl coefsX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl  /= !coefsX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite coefsX /= !simp.
Qed.

Lemma coefXM s i : ('Xs * s)``_i = (if (i == 0)%N then 0 else s``_i.-1).
Proof. by rewrite -commr_seriesX coefsMX. Qed.

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

Lemma derivX : 'Xs^``() = 1.
Proof. by apply/seriesP=> [[|i]]; rewrite coefs_deriv coefs1 coefsX ?mul0rn. Qed.


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
  apply/eqP; move: iv; apply contraLR; rewrite -leqNgt; exact: vmin.
- apply ValInf; apply seriesP => n; rewrite coefs0.
  apply/eqP; rewrite -(negbK (_ == 0)); apply/negP => Hn.
  by apply NPf; exists n.
Qed.

Lemma valuatNatP s n :
  reflect
    (s``_n != 0 /\ forall i, (i < n)%N -> s``_i = 0)
    (valuat s == Nat n).
Proof.
case: valuatP => [v Hv vmin /= |-> //]; apply (iffP eqP).
- by move=> [] <-{n}; split=>// i /vmin ->.
- move=> [Hn /(_ v)/contra_neqN/(_ Hv)]; rewrite -leqNgt => nlev.
  congr Nat; apply anti_leq; rewrite {}nlev andbT.
  by move: vmin => /(_ n)/contra_neqN/(_ Hn); rewrite -leqNgt.
- by [].
- by rewrite coefs0 eq_refl => [] [].
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite coefs0 eq_refl. Qed.
Lemma slead0 : slead 0 = 0.
Proof. by rewrite /slead valuat0. Qed.

Lemma valuat_seriesC c : valuat c%:S = if c == 0 then Inf else Nat 0.
Proof.
case: (altP (c =P 0)) => [->|]/=; first by rewrite valuat0.
case: valuatP => [n Hn Hmin Hc| /eqP]; last by rewrite seriesC_eq0 => ->.
congr Nat; apply/eqP; rewrite -leqn0.
move: Hn; apply: contra_neqT; rewrite -ltnNge => Hn.
by rewrite coefsC -[_ == _]negbK -lt0n Hn.
Qed.
Lemma slead_coefsC c : slead c%:S = c.
Proof.
by rewrite /slead valuat_seriesC; case: eqP => [->|_]; rewrite ?coefsC.
Qed.

Lemma valuatInfE s : (s == 0) = (valuat s == Inf).
Proof.
apply/eqP/eqP => [-> |]; first exact: valuat0.
by case: valuatP.
Qed.

Lemma sleadP s : (s == 0) = (slead s == 0).
Proof.
rewrite /slead; case: valuatP => [n Hn _|->]; last by rewrite !eqxx.
rewrite (negbTE Hn); apply/contraNF: Hn => /eqP ->.
by rewrite coefs0.
Qed.

Lemma valuat_opp s : valuat (- s) = valuat s.
Proof.
case: (valuatP s) => [v Hv vmin|->]; last by rewrite oppr0 valuat0.
apply/eqP/valuatNatP; split => [|i /vmin]; first by rewrite coefsN oppr_eq0.
by rewrite coefsN => ->; rewrite oppr0.
Qed.

Lemma valuatD s1 s2 :
  ((valuat s1) `&` (valuat s2) <= valuat (s1 + s2))%O.
Proof.
wlog v1lev2 : s1 s2 / (valuat s1 <= valuat s2)%O.
  move=> Hlog; case: (leP (valuat s1) (valuat s2)) => [|/ltW]/Hlog//.
  by rewrite addrC meetC.
rewrite (meet_idPl v1lev2); move: v1lev2.
case: (valuatP s2)=> [v2 _ v2min|->]; last by rewrite addr0 lexx.
case: (valuatP s1)=> [v1 _ v1min|->]; last by rewrite leInatbar.
case: valuatP => [v Hv _|_]; last by rewrite lex1.
rewrite !leEnatbar => v12.
move: Hv; rewrite coefsD leqNgt; apply: contra_neqN => Hv.
by rewrite (v1min _ Hv) (v2min _ (leq_trans Hv v12)) addr0.
Qed.

Lemma valuatDr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 + s2) = valuat s1.
Proof.
case: (valuatP s2) => [v2 _   v2min|-> _]; last by rewrite addr0.
case: (valuatP s1) => [v1 Hv1 v1min|->]; last by rewrite ltIbar.
rewrite ltEnatbar => v12; apply/eqP/valuatNatP.
split=> [|n nv1]; rewrite coefsD v2min ?addr0 // ?v1min //.
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

Lemma valuatMge s1 s2 :
  (addbar (valuat s1) (valuat s2) <= valuat (s1 * s2))%O.
Proof.
case: (valuatP s2)=> [v2 _ v2min|->]; last by rewrite mulr0 addbarI valuat0.
case: (valuatP s1)=> [v1 _ v1min|->]; last by rewrite mul0r addIbar valuat0.
case: valuatP => [v Hv _|]//=.
move: Hv; rewrite coefsM; apply contraR; rewrite -ltnNge => Hv.
apply/eqP/big1 => /= [[n]]; rewrite /= ltnS => Hn _.
case: (ltnP n v1) => [/v1min ->|v1n]; first by rewrite mul0r.
suffices {v1min v2min} /v2min -> : (v - n < v2)%N by rewrite mulr0.
by rewrite -(ltn_add2r n) subnK // addnC (leq_trans Hv) // leq_add2r.
Qed.


(** TODO : move this elsewhere and rename *)
Lemma inv1BcX c : (1 - c *: 'Xs) * \series c ^+ i .X^i = 1.
Proof.
apply/seriesP => n; rewrite coefsM big_ord_recl /=.
rewrite coefsB coefs1 coefsZ coefsX coefs_series /= !simp /= subr0 subn0.
case: n => [|n]; rewrite ?big_ord0 coefs1 /= ?addr0 ?expr0 ?mulr1 //.
rewrite big_ord_recl /bump /= !simp /=.
rewrite coefsB coefs1 coefsZ coefsX coefs_series /= !simp /=.
rewrite subSS subn0 mulNr -exprS subrr add0r.
rewrite /bump /=; apply big1 => [[i /= _] _].
by rewrite !add1n coefsB coefs1 coefsZ coefsX /= !simp mulNr mul0r oppr0.
Qed.

Lemma inv1BX c :  (1 - 'Xs) * \series 1 .X^i = 1.
Proof.
have:= inv1BcX 1; rewrite !scale1r => {2}<-; congr (_ * _).
by apply/seriesP => n; rewrite !coefs_series expr1n.
Qed.

Lemma inv1DX c :  (1 + 'Xs) * \series (-1)^+i .X^i = 1.
Proof. by have:= inv1BcX (-1); rewrite !scaleN1r opprK. Qed.

End FPSRing.


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


Section FPSComUnitRing.

Variable R : comUnitRingType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).


Definition unit_series : pred {series R} := fun s => (s``_0 \in GRing.unit).

Fixpoint inv_series_rec s bound n :=
  if bound is b.+1 then
    if (n <= b)%N then inv_series_rec s b n
    else - s``_0^-1 * \sum_(i < n) (inv_series_rec s b i) * s``_(n - i)
  else s``_0^-1.
Definition inv_series s : {series R} :=
  if unit_series s then \series inv_series_rec s i i .X^i else s.

Lemma coefs0_inv_series s : unit_series s -> (inv_series s)``_0 = s``_0^-1.
Proof. by rewrite /inv_series=> ->; rewrite /= coefs_series. Qed.

Lemma coefsS_inv_series s n :
  unit_series s ->
  (inv_series s)``_n.+1 =
  - s``_0^-1 * \sum_(i < n.+1) (inv_series s)``_i * s``_(n.+1 - i).
Proof.
move=> s_unit; rewrite /inv_series s_unit coefs_series /= ltnn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => Hi _.
rewrite coefs_series; congr (_ * _).
move: Hi => /subnKC <-; elim: (n - i)%N => [|{n} n IHn]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_seriesVr : {in unit_series, left_inverse 1 inv_series *%R}.
Proof.
move=> s s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/seriesP => n; elim: n {1 3 4}n (leqnn n) => [| n IHn] i.
  rewrite leqn0 => /eqP ->.
  rewrite coefsM big_ord_recr /= big_ord0.
  by rewrite add0r subnn coefs0_inv_series // mulVr // coefsC.
move=> Hi; case: (leqP i n) => [|Hni]; first exact: IHn.
have {Hi Hni i} -> : i = n.+1 by apply anti_leq; rewrite Hi Hni.
rewrite coefs1 /= coefsM big_ord_recr /= subnn mulrC coefsS_inv_series //.
by rewrite mulrA mulrN // mulrV // mulN1r subrr.
Qed.

Lemma unit_seriesP s t : t * s = 1 -> unit_series s.
Proof.
move/(congr1 (coefs 0)); rewrite /= coefs1 /= coefsM.
rewrite big_ord_recr big_ord0 /= add0r subnn mulrC => Heq.
rewrite /unit_series; apply/unitrPr; by exists t``_0.
Qed.

Lemma inv_series0id : {in [predC unit_series], inv_series =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_series unfold_in /unit_series => /negbTE ->.
Qed.

Definition series_comUnitMixin :=
  ComUnitRingMixin mul_seriesVr unit_seriesP inv_series0id.

Canonical series_unitRingType :=
  Eval hnf in UnitRingType {series R} series_comUnitMixin.
Canonical fpseries_unitRingType :=
  Eval hnf in [unitRingType of fpseries R for series_unitRingType].

Canonical series_unitAlgType := Eval hnf in [unitAlgType R of {series R}].
Canonical fpseries_unitAlgType := Eval hnf in [unitAlgType R of fpseries R].

Canonical series_comUnitRingType :=
  Eval hnf in [comUnitRingType of {series R}].
Canonical fpseries_comUnitRingType :=
  Eval hnf in [comUnitRingType of fpseries R].

Lemma coefsV0 s : unit_series s -> s^-1``_0 = s``_0^-1.
Proof. exact: coefs0_inv_series. Qed.

Lemma series_unitE s : (s \in GRing.unit) = (s``_0 \in GRing.unit).
Proof. by []. Qed.

Lemma seriesC_inv c : c%:S^-1 = (c^-1)%:S.
Proof.
have [/rmorphV-> // | nUc] := boolP (c \in GRing.unit).
by rewrite !invr_out // series_unitE coefsC /= (negbTE nUc).
Qed.

End FPSComUnitRing.


Section FPSIDomain.

Variable R : idomainType.

Implicit Types (a b c x y z : R) (s t r d : {series R}).


Lemma slead_valuatM s1 s2 :
  slead (s1 * s2) = slead s1 * slead s2 /\
  valuat (s1 * s2) = addbar (valuat s1) (valuat s2).
Proof.
have:= valuatMge s1 s2; rewrite /slead.
case: (valuatP s2)=> [v2 Hv2 v2min|->]; last by rewrite !mulr0 valuat0 addbarI.
case: (valuatP s1)=> [v1 Hv1 v1min|->]; last by rewrite !mul0r valuat0 addIbar.
have coefspv : (s1 * s2)``_(v1 + v2)%N = s1``_v1 * s2``_v2.
  rewrite coefsM (bigD1 (inord v1)); rewrite //= inordK ?ltnS ?leq_addr // addKn.
  rewrite (bigID (fun i => nat_of_ord i < v1)%N) /=.
  rewrite big1 => [|i /andP[_ /v1min]->]; rewrite ?mul0r // add0r.
  rewrite big1 => [|[i]/= Hi /andP[]]; first by rewrite addr0.
  rewrite -leqNgt /eq_op /= inordK ?ltnS ?leq_addr // => Hneq Hleq.
  suffices {v1min v2min} /v2min -> : (v1 + v2 - i < v2)%N by rewrite mulr0.
  have {Hneq Hleq} v1i : (v1 < i)%N by rewrite ltn_neqAle eq_sym Hneq Hleq.
  by rewrite ltnS in Hi; rewrite -(ltn_add2r i) subnK // addnC ltn_add2l.
case: (valuatP (s1 * s2)) => [v Hv vmin | Heq _] /=; first last.
- exfalso; move: Heq => /(congr1 (coefs (v1 + v2))).
  rewrite /= coefspv coefs0 => /eqP.
  by rewrite mulf_eq0 (negbTE Hv1) (negbTE Hv2).
- rewrite /= leEnatbar => lev.
  suffices -> : v = (v1 + v2)%N by rewrite coefspv.
  apply anti_leq; rewrite lev andbT leqNgt.
  apply: (contra_neqN (vmin (v1 + v2)%N)); rewrite coefspv.
  by rewrite mulf_eq0 negb_or Hv1 Hv2.
Qed.

Lemma valuatM s1 s2 : valuat (s1 * s2) = addbar (valuat s1) (valuat s2).
Proof. by have [_ ->] := slead_valuatM s1 s2. Qed.

Lemma sleadM s1 s2 : slead (s1 * s2) = slead s1 * slead s2.
Proof. by have [] := slead_valuatM s1 s2. Qed.


Fact series_idomainAxiom s t : s * t = 0 -> (s == 0) || (t == 0).
Proof. by move/eqP; rewrite !valuatInfE valuatM addbar_eqI. Qed.

Canonical series_idomainType :=
  Eval hnf in IdomainType {series R} series_idomainAxiom.
Canonical fpseries_idomainType :=
  Eval hnf in [idomainType of fpseries R for series_idomainType].

End FPSIDomain.
