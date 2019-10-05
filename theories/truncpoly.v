(** Truncated polynomial, i.e. polynom mod X^n *)

(*****************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple finfun bigop finset fingroup.
From mathcomp Require Import perm ssralg poly polydiv mxpoly binomial bigop.
From mathcomp Require Import finalg zmodp matrix mxalgebra polyXY ring_quotient.
From mathcomp Require Import generic_quotient.

Require Import auxresults.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
(* Local Open Scope quotient_scope. *)

Delimit Scope tfps_scope with tfps.

Reserved Notation "{ 'trpoly' R n }"
         (at level 0, R at next level, format "{ 'trpoly'  R  n }").
Reserved Notation "[ 'trpoly' s <= n => F ]"
  (at level 0, n at next level, s ident, format "[ 'trpoly' s <= n  =>  F ]").
Reserved Notation "[ 'trpoly' s => F ]"
  (at level 0, s ident, format "[ 'trpoly'  s  =>  F ]").
Reserved Notation "c %:S" (at level 2).
Reserved Notation "f *h g" (at level 2).
Reserved Notation "f ^` ()" (at level 8).

Section PolyCompl.

Lemma poly_cat (R : ringType) (p : {poly R}) n :
  p = Poly (take n p) + 'X^n * Poly (drop n p).
Proof.
apply/polyP=> i; rewrite coefD coefXnM !coef_Poly; case: ltnP => Hi.
by rewrite nth_take // addr0.
rewrite nth_drop subnKC // [(take _ _)`_i]nth_default ?add0r //.
by rewrite size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

End PolyCompl.


Section PolyModXnDef.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}).

Record trunc_polynomial :=
  TruncPolynomial { trpoly :> {poly R}; _ : size trpoly <= n.+1 }.

Canonical trunc_polynomial_subType :=
  Eval hnf in [subType for trpoly].
Definition trunc_polynomial_eqMixin :=
  Eval hnf in [eqMixin of trunc_polynomial by <:].
Canonical trunc_polynomial_eqType :=
  Eval hnf in EqType trunc_polynomial trunc_polynomial_eqMixin.
Definition trunc_polynomial_choiceMixin :=
  [choiceMixin of trunc_polynomial by <:].
Canonical trunc_polynomial_choiceType :=
  Eval hnf in ChoiceType trunc_polynomial trunc_polynomial_choiceMixin.

Lemma trpoly_inj : injective trpoly. Proof. exact: val_inj. Qed.

Definition trpoly_of of phant R := trunc_polynomial.
Identity Coercion type_trpoly_of : trpoly_of >-> trunc_polynomial.

Lemma size_trpoly (f : trpoly_of (Phant R)) : size f <= n.+1.
Proof. by case: f. Qed.

End PolyModXnDef.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope ring_scope with trpoly_of.
Bind Scope ring_scope with trunc_polynomial.
Arguments trpoly {R} n%N.
Arguments trpoly_inj {R} [p1%R p2%R] : rename.
Notation "{ 'trpoly' R n }" :=  (trpoly_of n (Phant R)).

Hint Resolve size_trpoly.


Section Quotient.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}) (f g : {trpoly R n}).

Lemma coef_trpoly f i : f`_i = if i <= n then f`_i else 0.
Proof.
case: (leqP i n) => Hi //.
by rewrite nth_default // (leq_trans (size_trpoly _) Hi).
Qed.

Lemma trpolyP f g : (forall i, i <= n -> f`_i = g`_i) <-> (f = g).
Proof.
split => [H | H i Hi].
- apply/val_inj/polyP => i; rewrite [LHS]coef_trpoly [RHS]coef_trpoly.
  by case: leqP => //; apply: H.
- move: H => /(congr1 val)/(congr1 (fun r => r`_i)).
  by rewrite coef_trpoly Hi.
Qed.

Definition Trpoly_of (p : {poly R}) (p_small : size p <= n.+1)
  : {trpoly R n} := TruncPolynomial p_small.
Definition trpoly_of_fun (f : nat -> R) := Trpoly_of (size_poly _ f).

Lemma trXn_spec p : size (Poly (take n.+1 p)) <= n.+1.
Proof. by apply: (leq_trans (size_Poly _)); rewrite size_take geq_minl. Qed.
Definition trXn p : {trpoly R n} := TruncPolynomial (trXn_spec p).

Lemma trXnE p : Poly (take n.+1 p) = val (trXn p).
Proof. by []. Qed.

Lemma coef_trXn p i : (trXn p)`_i = if i <= n then p`_i else 0.
Proof.
rewrite coef_trpoly; case: leqP => Hi //.
by rewrite /= coef_Poly nth_take.
Qed.

Lemma trXnP p q : (forall i, i <= n -> p`_i = q`_i) <-> (trXn p = trXn q).
Proof.
rewrite -trpolyP; split => H i Hi.
- by rewrite !coef_trXn Hi; apply H.
- by have := H i Hi; rewrite !coef_trXn Hi.
Qed.

Lemma trpolyK : cancel (trpoly n) trXn.
Proof. by move=> f; apply/trpolyP => i Hi; rewrite coef_trXn Hi. Qed.

Lemma trXnK (p : {trpoly R n}) : trXn p = p :> {poly R}.
Proof. exact: (congr1 val (trpolyK p)). Qed.

Lemma Poly_takeK (p : {trpoly R n}) : Poly (take n.+1 p) = p.
Proof. exact: (congr1 val (trpolyK p)). Qed.

Lemma nth0_trXn (p : {poly R}) : (trXn p)`_0 = p`_0.
Proof. by rewrite coef_trXn leq0n. Qed.

Lemma coef_trpoly_of_fun (f : nat -> R) i :
  (trpoly_of_fun f)`_i = if i <= n then f i else 0.
Proof. by rewrite /trpoly_of_fun coef_poly ltnS. Qed.


Definition poly_trXn_class := QuotClass trpolyK.
Canonical poly_trXn_type := QuotType {trpoly R n} poly_trXn_class.

Lemma poly_trXn_quotP p q :
  reflect
    (forall i, (i <= n)%N -> p`_i = q`_i)
    (p == q %[mod {trpoly R n}])%qT.
Proof. by rewrite !unlock /pi_phant; apply (iffP eqP); rewrite trXnP. Qed.

End Quotient.


Section MorePolyTheory.

Variable (R : ringType).

Lemma leq_size_deriv (p : {poly R}) : (size p^`() <= (size p).-1)%N.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
by rewrite -ltnS prednK // ?lt_size_deriv // size_poly_gt0.
Qed.

Lemma p_neq0 (p : {poly R}): (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
by move => [x px_neq0]; move: px_neq0; apply: contra => /eqP ->; rewrite horner0.
Qed.

Variable (K : idomainType).

Fact polyXP (p : {poly K}) : reflect (p`_0 = 0) ('X %| p).
Proof. by rewrite -['X]subr0 -polyC0 -horner_coef0; apply: polyXsubCP. Qed.

Fact nth0_eq_nth0 (p q : {poly K}) :
   p %= q -> (p`_0 == 0) = (q`_0 == 0).
Proof.
move => p_eqp_q; rewrite -!horner_coef0.
apply/(sameP eqP).
apply/(equivP eqP).
apply: (rwP2 (polyXsubCP _ _)).
apply: (aux_equivb (polyXsubCP _ _)).
by apply: eqp_dvdr.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Fact size_deriv (p : {poly K}) : size (p ^`()%R) = (size p).-1.
Proof.
have [lt_sp_1 | le_sp_1] := ltnP (size p) 2.
  move: (size1_polyC lt_sp_1) => ->.
  by rewrite derivC size_poly0 size_polyC ; case: (_ != _).
rewrite size_poly_eq // !prednK ; last first.
  move: (ltn_predK le_sp_1) => H.
  by move: le_sp_1 ; rewrite -{1}H -[X in _ < X]add1n -add1n leq_add2l.
rewrite -mulr_natr mulf_eq0 ; apply/norP ; split.
  by rewrite -lead_coefE lead_coef_eq0 -size_poly_gt0 (ltn_trans _ le_sp_1).
move: (charf0P K) => char_K_property.
move/char_K_property : char_K_is_zero => char_K.
rewrite char_K -lt0n.
move: (ltn_predK le_sp_1) => H.
by move: le_sp_1 ; rewrite -{1}H -[X in _ < X]add1n -add1n leq_add2l.
Qed.

Lemma p_cst (p : {poly K}) : p ^`() = 0 -> {c : K | p = c %:P}.
Proof.
move/eqP ; rewrite -size_poly_eq0 size_deriv.
move/eqP => H_size_p.
exists p`_0 ; apply: size1_polyC.
by rewrite (leq_trans (leqSpred _)) // H_size_p.
Qed.

End MorePolyTheory.


Section ModPolyTheory.

Variable (R : ringType).
Implicit Types (p q r s : {poly R}).

Fact leq_modpXn m p : size (trXn m p) <= m.+1.
Proof. by case: (trXn _ _). Qed.

(* should not be visible outside this file *)
Fact trXnC a n : trXn n a%:P = a%:P :> {poly R}.
Proof.
apply/polyP => i; rewrite coef_trXn coefC.
by case: eqP => [->|_] //; rewrite if_same.
Qed.

Fact trXn_trXn p m n : m <= n -> trXn m (trXn n p) = trXn m p.
Proof.
move=> le_mn; apply/trXnP => i le_im.
by rewrite coef_trXn (leq_trans le_im le_mn).
Qed.

Fact coef0M p q : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed.

Lemma trXn_mull n p q : trXn n (val (trXn n p) * q) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans le_ji le_in).
Qed.

Lemma trXn_mulr n p q : trXn n (p * val (trXn n q)) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans (leq_subr _ _) le_in).
Qed.

Lemma trXn_mul n p q :
  trXn n (val (trXn n p) * val (trXn n q)) = trXn n (p * q).
Proof. by rewrite trXn_mulr trXn_mull. Qed.

Variable (n : nat).

(* zmodType structure *)
Implicit Types (f g : {trpoly R n}).

Fact zero_trpoly_subproof : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.
Definition zero_trpoly := Trpoly_of zero_trpoly_subproof.

Lemma add_trpoly_subproof f g :
  size (val f + val g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_trpoly. Qed.
Definition add_trpoly f g := Trpoly_of (add_trpoly_subproof f g).

Lemma opp_trpoly_proof f : size (- val f) <= n.+1.
Proof. by rewrite size_opp ?size_trpoly. Qed.
Definition opp_trpoly f := Trpoly_of (opp_trpoly_proof f).

Program Definition trpoly_zmodMixin :=
  @ZmodMixin {trpoly R n} zero_trpoly opp_trpoly add_trpoly _ _ _ _.
Next Obligation. by move => f1 f2 f3; apply/val_inj; apply: addrA. Qed.
Next Obligation. by move => f1 f2; apply/val_inj; apply: addrC. Qed.
Next Obligation. by move => f; apply/val_inj; apply: add0r. Qed.
Next Obligation. by move => f; apply/val_inj; apply: addNr. Qed.
Canonical trpoly_zmodType := ZmodType {trpoly R n} trpoly_zmodMixin.

Lemma trXn0 : trXn n 0 = 0.
Proof. by apply/val_inj => /=; rewrite polyseq0. Qed.

Fact trXn_is_additive : additive (trXn n).
Proof.
by move=> f g; apply/trpolyP => i Hi; rewrite coefB !coef_trXn coefB Hi.
Qed.
Canonical trXn_additive := Additive trXn_is_additive.

Fact trpoly_is_additive : additive (trpoly n : {trpoly R n} -> {poly R}).
Proof. by []. Qed.
Canonical trpoly_additive := Additive trpoly_is_additive.


(* ringType structure *)
Fact one_trpoly_proof : size (1 : {poly R}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.
Definition one_trpoly : {trpoly R n} := Trpoly_of one_trpoly_proof.

Definition mul_trpoly f g := trXn n (val f * val g).

Local Notation "[ 'trpoly' s => F ]" := (trpoly_of_fun n (fun s => F)).
Definition hmul_trpoly f g := trpoly_of_fun n (fun j => (f`_j * g`_j)).

Definition deriv_trpoly f : {trpoly R n.-1} :=
  trpoly_of_fun n.-1 (fun j => f`_j.+1 *+ j.+1).

Local Notation "f *h g" := (hmul_trpoly f g) (at level 2).

Lemma hmul_trpolyA : associative hmul_trpoly.
Proof.
by move=> f1 f2 f3; apply/trpolyP => i Hi; rewrite !coef_poly ltnS Hi mulrA.
Qed.

Lemma hmul_trpoly0r f : 0 *h f = 0.
Proof. by apply/trpolyP => i Hi; rewrite coef_poly coef0 mul0r if_same. Qed.

Lemma hmul_trpolyr0 f : f *h 0 = 0.
Proof. by apply/trpolyP => i Hi; rewrite coef_poly coef0 mulr0 if_same. Qed.

Program Definition trpoly_ringMixin :=
  @RingMixin [zmodType of {trpoly R n}] one_trpoly mul_trpoly _ _ _ _ _ _.
Next Obligation.
by move=> f1 f2 f3 /=; rewrite /mul_trpoly trXn_mulr trXn_mull mulrA.
Qed.
Next Obligation. by move=> p; apply val_inj; rewrite /= mul1r Poly_takeK. Qed.
Next Obligation. by move=> p; apply val_inj; rewrite /= mulr1 Poly_takeK. Qed.
Next Obligation.
by move=> f1 f2 f3; apply val_inj => /=; rewrite mulrDl !trXnE raddfD.
Qed.
Next Obligation.
by move=> f1 f2 f3; apply val_inj => /=; rewrite mulrDr !trXnE raddfD.
Qed.
Next Obligation. by rewrite -val_eqE oner_neq0. Qed.
Canonical trpoly_ringType := RingType {trpoly R n} trpoly_ringMixin.

Lemma trpoly1E : Poly (take n.+1 (1 : {trpoly R n})) = 1.
Proof. by apply/polyP => i; rewrite coef_Poly polyseq1. Qed.

Lemma trXn1 : trXn n 1 = 1.
Proof. by apply/val_inj => /=; rewrite trpoly1E. Qed.

Fact trXn_is_multiplicative : multiplicative (@trXn R n).
Proof. by split => [f g|] /=; [rewrite -trXn_mul | rewrite trXn1]. Qed.
Canonical trXn_multiplicative := AddRMorphism trXn_is_multiplicative.

Fact mul_trpoly_val f g : f * g = trXn n ((val f) * (val g)).
Proof. by []. Qed.

Fact exp_trpoly_val f (m : nat) : f ^+ m = trXn n ((val f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphX /= trpolyK -exprS.
Qed.

(* lmodType structure *)
Lemma scale_trpoly_spec (c : R) f : size (c *: val f) <= n.+1.
Proof. exact: leq_trans (size_scale_leq _ _) (size_trpoly _). Qed.

Definition scale_trpoly (c : R) f : {trpoly R n} :=
  TruncPolynomial (scale_trpoly_spec c f).

Program Definition trpoly_lmodMixin :=
  @LmodMixin R [zmodType of {trpoly R n}] scale_trpoly _ _ _ _.
Next Obligation. by apply/trpolyP => i le_in /=; rewrite !coefZ mulrA. Qed.
Next Obligation. by move=> x; apply/trpolyP => i le_in /=; rewrite scale1r. Qed.
Next Obligation. by move=> r x y; apply/trpolyP => i /=; rewrite scalerDr. Qed.
Next Obligation. by move=> r s; apply/trpolyP => i /=; rewrite scalerDl. Qed.
Canonical trpoly_lmodType :=
  Eval hnf in LmodType R {trpoly R n} trpoly_lmodMixin.

Fact trXn_is_linear : linear (@trXn R n).
Proof. move=> c f g; apply/trpolyP => i Hi.
by rewrite coefD coefZ !coef_trXn Hi coefD coefZ.
Qed.
Canonical trXn_linear := AddLinear trXn_is_linear.

Fact trpoly_is_linear : linear (@trpoly R n : {trpoly R n} -> {poly R}).
Proof. by []. Qed.
Canonical trpoly_linear := AddLinear trpoly_is_linear.


(* lalgType structure *)
Fact scale_trpolyAl c f g : scale_trpoly c (f * g) = (scale_trpoly c f) * g.
Proof. by apply val_inj; rewrite /= -linearZ /= -scalerAl !trXnE linearZ. Qed.
Canonical trpoly_lalgType :=
  Eval hnf in LalgType R {trpoly R n} scale_trpolyAl.
Canonical trXn_lrmorphism := AddLRMorphism trXn_is_linear.

Local Notation "c %:S" := (trXn _ (c %:P)) (at level 2).

Fact onefE : 1 = 1 %:S.
Proof. by apply/val_inj => /=; rewrite -[LHS](trXnC 1 n). Qed.

(* Test *)
Fact trpoly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Fact trpoly1 : trXn n (1 : {poly R}) = 1.
Proof. by rewrite rmorph1. Qed.

End ModPolyTheory.

Notation "c %:S" := (trXn _ (c %:P)) (at level 2) : tfps_scope.
Local Open Scope tfps_scope.


Section ModPolyTheoryComRing.

Variable (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact mul_trpolyC f g : f * g = g * f.
Proof. by apply val_inj => /=; rewrite mulrC. Qed.
Canonical trpoly_comRingType :=
  Eval hnf in ComRingType {trpoly R n} mul_trpolyC.
Canonical trpoly_algType := Eval hnf in CommAlgType R {trpoly R n}.

Lemma hmul_trpolyC : commutative (@hmul_trpoly R n).
Proof.
by move=> f1 f2; apply/trpolyP => /= i; rewrite !coef_poly mulrC.
Qed.

End ModPolyTheoryComRing.


Section ModPolyTheoryUnitRing.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition unit_trpoly : pred {trpoly R n} := fun f => f`_0 \in GRing.unit.

(* Noncommutative setting : we define a left and right inverve, getting  *)
(* that they are equal only latter thank to general semigroup theory.    *)
Fixpoint inv_trpoly_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then inv_trpoly_rec f b m
    else - (\sum_(i < m) (inv_trpoly_rec f b i) * f`_(m - i)) * f`_(locked 0%N)^-1
  else f`_(locked 0%N)^-1.
Definition inv_trpoly f : {trpoly R n} :=
  if unit_trpoly f then trpoly_of_fun n (fun i => inv_trpoly_rec f i i) else f.

Fixpoint inv_trpolyr_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then inv_trpolyr_rec f b m
    else - f`_(locked 0%N)^-1 *
           (\sum_(i < m) f`_(locked i.+1) * (inv_trpolyr_rec f b (m - i.+1)%N))
  else f`_(locked 0%N)^-1.
Definition inv_trpolyr f : {trpoly R n} :=
  if unit_trpoly f then trpoly_of_fun n (fun i => inv_trpolyr_rec f i i) else f.

Lemma coef0_inv_trpoly f : unit_trpoly f -> (inv_trpoly f)`_0 = f`_0^-1.
Proof. by rewrite /inv_trpoly => ->; rewrite coef_trpoly_of_fun /= -lock. Qed.
Lemma coef0_inv_trpolyr f : unit_trpoly f -> (inv_trpolyr f)`_0 = f`_0^-1.
Proof. by rewrite /inv_trpolyr => ->; rewrite coef_trpoly_of_fun /= -lock. Qed.

Lemma coefS_inv_trpoly f m :
  unit_trpoly f -> m < n ->
  (inv_trpoly f)`_m.+1 =
  - (\sum_(i < m.+1) (inv_trpoly f)`_i * f`_(m.+1 - i)) * f`_(locked 0%N)^-1.
Proof.
move=> s_unit lt_mn.
rewrite /inv_trpoly s_unit coef_trpoly_of_fun /= ltnn lt_mn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => le_im _.
rewrite coef_trpoly_of_fun (leq_trans le_im (ltnW lt_mn)); congr (_ * _).
have:= le_im => /subnKC <-; elim: (m - i)%N => [|k IHk]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.
Lemma coefS_inv_trpolyr f m :
  unit_trpoly f -> m < n ->
  (inv_trpolyr f)`_m.+1 =
  - f`_(locked 0%N)^-1 *
    (\sum_(i < m.+1) f`_(locked i.+1) * (inv_trpolyr f)`_(m - i)%N).
Proof.
move=> s_unit lt_mn.
rewrite /inv_trpolyr s_unit coef_trpoly_of_fun /= ltnn lt_mn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => le_im _.
rewrite coef_trpoly_of_fun (leq_trans (leq_subr _ _) (ltnW lt_mn)); congr (_ * _).
rewrite /bump /= subSS.
move: (m - i)%N (leq_subr i m) {le_im} => {i} i le_im.
move: le_im => /subnKC <-; elim: (m - i)%N => [|k IHl]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_trpolyVr : {in unit_trpoly, left_inverse 1 inv_trpoly *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/trpolyP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  rewrite [0%N]lock /= coef_Poly nth_take -lock //.
  rewrite coefM big_ord_recr big_ord0 sub0n [0%N]lock /=.
  by rewrite /= add0r -lock coef0_inv_trpoly // mulVr // coefC.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/= [m.+1]lock /= coef_Poly.
case: (ltnP m.+1 n.+1) => Hmn.
  rewrite nth_take -lock //.
  rewrite coefM big_ord_recr [m.+1]lock /= subnn -lock coefS_inv_trpoly //.
  by rewrite -lock divrK // subrr.
by rewrite nth_default // size_take -lock (leq_trans (geq_minl _ _)).
Qed.

Lemma mul_trpolyrVr : {in unit_trpoly, right_inverse 1 inv_trpolyr *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/trpolyP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  rewrite [0%N]lock /= coef_Poly nth_take -lock //.
  rewrite coefM big_ord_recr big_ord0 sub0n [0%N]lock /=.
  by rewrite /= add0r -lock coef0_inv_trpolyr // mulrV // coefC.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/= [m.+1]lock /= coef_Poly.
case: (ltnP m.+1 n.+1) => Hmn.
  rewrite nth_take -lock //.
  rewrite coefM big_ord_recl [m.+1]lock [val ord0]/= subn0.
  rewrite -lock coefS_inv_trpolyr //.
  rewrite mulNr mulrN -lock mulVKr // addrC.
  apply/eqP; rewrite subr_eq0; apply/eqP.
  by apply eq_bigr => [] [i] /=; rewrite -lock.
by rewrite nth_default // size_take -lock (leq_trans (geq_minl _ _)).
Qed.

(* General semi-group theory : left inverse = right inverse *)
Lemma unit_trpolyE f : unit_trpoly f -> inv_trpoly f = inv_trpolyr f.
Proof.
move=> H; have:= erefl (inv_trpoly f * f * inv_trpolyr f).
by rewrite -{1}mulrA mul_trpolyVr // mul1r mul_trpolyrVr // mulr1.
Qed.

Lemma mul_trpolyrV : {in unit_trpoly, right_inverse 1 inv_trpoly *%R}.
Proof. by move=> f Hs; rewrite unit_trpolyE // mul_trpolyrVr. Qed.

Lemma unit_trpolyP f g : g * f = 1 /\ f * g = 1 -> unit_trpoly f.
Proof.
move=> [] /(congr1 val)/(congr1 (coefp (locked 0%N))) /=.
rewrite coef_Poly nth_take -lock // coef1 coef0M eq_refl => Hl.
move=>    /(congr1 val)/(congr1 (coefp (locked 0%N))) /=.
rewrite coef_Poly nth_take -lock // coef1 coef0M eq_refl => Hr.
by rewrite /unit_trpoly; apply/unitrP; exists g`_0.
Qed.

Lemma inv_trpoly0id : {in [predC unit_trpoly], inv_trpoly =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_trpoly unfold_in /unit_trpoly => /negbTE ->.
Qed.

Definition trpoly_unitMixin :=
  UnitRingMixin mul_trpolyVr mul_trpolyrV unit_trpolyP inv_trpoly0id.
Canonical trpoly_unitRingType :=
  Eval hnf in UnitRingType {trpoly R n} trpoly_unitMixin.

Lemma coefsV0 f : unit_trpoly f -> f^-1`_0 = f`_0^-1.
Proof. exact: coef0_inv_trpoly. Qed.

Lemma trpoly_unitE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma coef_inv_trpoly f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_j.+1 * f^-1`_(i - j.+1)).
Proof.
move=> funit; case: ltnP => Hi.
  by rewrite -(trpolyK f^-1) coef_trXn leqNgt Hi.
case: i Hi => [|i] Hi; first by rewrite eq_refl coefsV0.
have -> : f^-1 = inv_trpoly f by [].
rewrite unit_trpolyE // coefS_inv_trpolyr // -!lock; congr (_ * _).
by apply eq_bigr => /= j _; rewrite -lock subSS.
Qed.

Local Notation "f *h g" := (hmul_trpoly f g) (at level 2).

Lemma hmul_trpolyr1 f : f *h 1 = trXn n (f`_0)%:P.
Proof.
apply/trpolyP => i.
rewrite coef_trXn coefC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_trpoly1r f : 1 *h f = trXn n (f`_0)%:P.
Proof.
apply/trpolyP => i.
rewrite coef_trXn coefC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mul1r ?mul0r.
Qed.

Fact nth0_mul_trpoly f g : (f * g)`_0 = f`_0 * g`_0.
Proof. by rewrite coef_trXn coef0M. Qed.

Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
have [f_unit|] := boolP (f \is a GRing.unit); first by rewrite coef_inv_trpoly.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite trpoly_unitE => /invr_out ->.
Qed.

Lemma trpolyC_inv (c : R) : (trXn n c%:P)^-1 = trXn n (c^-1)%:P.
Proof.
have [Uc | nUc] := boolP (c \in GRing.unit).
  by rewrite -/((trXn n \o @polyC R) _) -rmorphV.
by rewrite !invr_out // trpoly_unitE coef_trXn coefC.
Qed.

End ModPolyTheoryUnitRing.


Section ModPolyTheoryComUnitRing.

Variable (R : comUnitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Canonical trpoly_comUnitRingType := [comUnitRingType of {trpoly R n}].
Canonical trpoly_unitAlgType := Eval hnf in [unitAlgType R of {trpoly R n}].

(* tests *)

Lemma trXn_is_unit (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite trpoly_unitE nth0_trXn. Qed.

Lemma trpoly_is_cst (g : {trpoly R 0}) : g = (g`_0) %:S.
Proof.
apply/val_inj => /=.
have /= -> := trXnC g`_0 0.
by apply: size1_polyC; rewrite size_trpoly.
Qed.

Lemma trpolyC_mul :
  {morph (fun x => (x%:S : {trpoly R n})) : a b / a * b >-> a * b}.
Proof. by move=> a b; apply val_inj; rewrite /= polyC_mul trXnE -trXn_mul. Qed.

End ModPolyTheoryComUnitRing.


Section ModPolyTheoryIDomain.

Variable R : idomainType.

Lemma poly_modXn n (p : {poly R}) : p %% 'X^n = Poly (take n p).
Proof.
rewrite {1}(poly_cat p n) addrC mulrC Pdiv.IdomainUnit.modp_addl_mul_small //.
- by rewrite lead_coefXn unitr1.
- rewrite size_polyXn ltnS (leq_trans (size_Poly _)) //.
  by rewrite size_take -/(minn _ _) geq_minl.
Qed.


Lemma trXn_modE m (p : {poly R}) : p %% 'X^ m.+1 = trXn m p.
Proof. by apply/val_inj => /=; rewrite poly_modXn. Qed.

Fact trpoly_modp (n m : nat) (p : {poly R}) : n <= m ->
  trXn n (p %% 'X^m.+1) = trXn n p.
Proof.
by move=> lt_nm; apply/val_inj; rewrite /= trXn_modE !trXnE trXn_trXn.
Qed.

Variable n : nat.
Implicit Types (f g : {trpoly R n}).

Fact mod_trpoly (m : nat) f : n <= m -> f %% 'X^m.+1 = (val f).
Proof.
move=> leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_trpoly _)).
Qed.

End ModPolyTheoryIDomain.

Fact trXn_eq0 (R : ringType) n m (p : {poly R}) :
  p`_0 = 0 -> n < m -> trXn n (p ^+ m) = 0.
Proof.
elim: m n p => [|m IHm] n p Hp; first by rewrite ltn0.
case: n => [_|n]/=.
- apply/trpolyP => i /=; rewrite coef_trXn coef0 leqn0.
  case: eqP => [->|] // _.
  suff -> : (p ^+ m.+1)`_0 = (p`_0) ^+ m.+1 by rewrite Hp expr0n.
  elim: m.+1 {IHm} => {m}[|m IHm]; first by rewrite !expr0 coef1 eq_refl.
  by rewrite !exprS -{}IHm coefM big_ord_recl big_ord0 addr0.
rewrite ltnS exprS => lt_nm.
apply/trpolyP => i /= le_in1; rewrite coef_trXn coef0 le_in1.
rewrite coefM; apply big1 => [] [j]; rewrite /= ltnS => le_ji _.
case: j le_ji => [|j]; first by rewrite Hp mul0r.
case: i le_in1 => [|i]; first by rewrite ltn0.
rewrite !ltnS subSS => le_in le_ji.
have := (IHm _ _ Hp lt_nm).
move=> /(congr1 (fun x : {trpoly _ _} => x`_(i - j))).
rewrite coef0 coef_trXn (leq_trans (leq_subr _ _) le_in) => ->.
by rewrite mulr0.
Qed.


Section MapTrpoly.

Variables (K L : ringType) (n : nat) (f : {rmorphism K -> L}).

Implicit Type g h : {trpoly K n}.

Fact map_trpoly_spec g : size (map_poly f (val g)) <= n.+1.
Proof.
by rewrite map_polyE (leq_trans (size_Poly _)) // size_map size_trpoly.
Qed.
Definition map_trpoly g : {trpoly L n} := TruncPolynomial (map_trpoly_spec g).

Lemma map_trpolyM g h : map_trpoly (g * h) = (map_trpoly g) * (map_trpoly h).
Proof.
apply/trpolyP => i Hi.
rewrite coef_map /= !coef_Poly !nth_take //.
rewrite !coefM rmorph_sum; apply eq_bigr => [] [j]; rewrite /= ltnS => le_ji _.
by rewrite rmorphM !coef_map.
Qed.

Fact map_trpoly_is_additive : additive map_trpoly.
Proof. by move => x y; apply/val_inj => /=; rewrite rmorphB. Qed.
Canonical map_trpoly_additive := Additive map_trpoly_is_additive.

Fact map_trpoly_is_multiplicative : multiplicative map_trpoly.
Proof.
split => [x y|]; first by rewrite map_trpolyM.
by apply/val_inj => /=; rewrite rmorph1.
Qed.
Canonical map_trpoly_rmorphism := AddRMorphism map_trpoly_is_multiplicative.

Lemma map_trpolyZ (c : K) g : map_trpoly (c *: g) = (f c) *: (map_trpoly g).
Proof. by apply/trpolyP => i le_in; rewrite linearZ /= map_polyZ. Qed.
Canonical map_trpoly_linear := let R := {trpoly K n} in
  AddLinear (map_trpolyZ : scalable_for (f \; *:%R) map_trpoly).
Canonical map_trpoly_lrmorphism := [lrmorphism of map_trpoly].

(* tests *)
Fact test_map_trpoly0 : map_trpoly 0 = 0.
Proof. by rewrite linear0. Qed.

Fact test_map_trpolyD g h : map_trpoly (g + h) = (map_trpoly g) + (map_trpoly h).
Proof. by rewrite linearD. Qed.

Lemma trXn_map_poly (p : {poly K}) :
  @trXn L n (map_poly f p) = map_trpoly (trXn n p).
Proof.
apply/trpolyP => i le_in.
by rewrite coef_trXn le_in /= !coef_map coef_Poly nth_take.
Qed.

Local Notation "g '^f'" := (map_trpoly g).
Local Notation "f *h g" := (hmul_trpoly f g) (at level 2).

Lemma map_hmul g h : (g *h h) ^f = (g ^f) *h (h ^f).
Proof.
apply/trpolyP => i le_in /=.
rewrite coef_map !coef_poly ltnS le_in [LHS]rmorphM.
have co (l : {trpoly K n}) : (if i < size l then f l`_i else 0) = f l`_i.
  by case: ltnP => // H; rewrite nth_default // rmorph0.
by rewrite !co.
Qed.

End MapTrpoly.

Lemma map_trpoly_injective (K L : ringType) n (f : {injmorphism K -> L}) :
  injective (@map_trpoly _ _ n f).
Proof. by move=> x y /val_eqP/eqP /= /map_poly_injective H; apply val_inj. Qed.

Lemma map_trpoly_inj (K : fieldType) (L : ringType) n (f : {rmorphism K -> L}) :
  injective (@map_trpoly _ _ n f).
Proof. by move=> x y /val_eqP/eqP /= /map_poly_inj H; apply val_inj. Qed.


Section IdFun.

Lemma map_poly_idfun (R : ringType) : map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma idfun_injective A : injective (@idfun A). Proof. done. Qed.
Canonical idfun_is_injmorphism (A : ringType) :=
    InjMorphism (@idfun_injective A).

End IdFun.

Lemma map_trpoly_idfun (K : fieldType) (m : nat) :
  map_trpoly [rmorphism of (@idfun K)] =1 @idfun {trpoly K m}.
Proof. by move=> f; apply/trpolyP => i le_in /=; rewrite map_poly_idfun. Qed.

