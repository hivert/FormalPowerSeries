(** Truncated polynomial, i.e. polynom mod X^n *)
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

Delimit Scope trpoly_scope with trpoly.

Reserved Notation "{ 'trpoly' R n }"
         (at level 0, R, n at level 2, format "{ 'trpoly'  R  n }").
Reserved Notation "[ 'trpoly' s <= n => F ]"
  (at level 0, n at next level, s ident, format "[ 'trpoly' s <= n  =>  F ]").
Reserved Notation "[ 'trpoly' s => F ]"
  (at level 0, s ident, format "[ 'trpoly'  s  =>  F ]").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\X" (at level 0).
Reserved Notation "\Xo( n )" (at level 0).
Reserved Notation "f *h g" (at level 2).
Reserved Notation "x ^^ n" (at level 29, left associativity).
Reserved Notation "f \So g" (at level 50).
Reserved Notation "\sqrt f" (at level 10).


Section MoreBigop.

Definition swap (R : Type) (x : R * R) := (x.2, x.1).

Lemma swap_inj (R : Type) : involutive (@swap R).
Proof. by move => [x1 x2]. Qed.

Variables (R : Type).

Lemma triangular_swap (idx : R) (op : Monoid.com_law idx)
      (m : nat) (P : 'I_m -> 'I_m -> bool) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | P i j) F i j =
  \big[op/idx]_(j < m) \big[op/idx]_(i < m | P i j) F i j.
Proof. by rewrite !pair_big_dep (reindex_inj (inv_inj (@swap_inj _))). Qed.

Variable (idx : R) (op : Monoid.com_law idx).

Lemma index_translation (m j : nat) (F : nat -> R) :
  \big[op/idx]_(i < m - j) F i =
  \big[op/idx]_(k < m | j <= k)  F (k - j)%N.
Proof.
rewrite -(big_mkord predT F) /= (big_mknat _ j m (fun k => F (k - j)%N)).
rewrite -{2}[j]add0n (big_addn 0 m j _ _).
by apply: eq_bigr => i _ ; rewrite addnK.
Qed.

Lemma aux_triangular_index_bigop (m : nat) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < m) F i j =
  \big[op/idx]_(k < m) \big[op/idx]_(l < k.+1) F l (k - l)%N.
Proof.
evar (G : 'I_m -> R) ; rewrite [LHS](eq_bigr G) => [|i _] ; last first.
- rewrite (eq_bigl (fun j => nat_of_ord j < (m - (nat_of_ord i))%N))=> [|j /=].
  + rewrite big_ord_narrow => [ | _ /= ] ; first exact: leq_subr.
    by rewrite index_translation; symmetry; rewrite /G; reflexivity.
  + by rewrite ltn_subRL.
- rewrite /G (triangular_swap _ (fun i k => (nat_of_ord i) <= (nat_of_ord k))
                                (fun i k => F i (k - i)%N)).
  apply: eq_big => [ // | i _].
  rewrite (eq_bigl (fun i0 => (nat_of_ord i0) < i.+1)) => [ | j ] ; last first.
  + by rewrite -ltnS.
  + by rewrite big_ord_narrow.
Qed.

Lemma triangular_index_bigop (m n: nat) (F : nat -> nat -> R) :
  n <= m ->
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < n) F i j =
  \big[op/idx]_(k < n) \big[op/idx]_(l < k.+1) F l (k - l)%N.
Proof.
move => leq_nm.
rewrite -(subnKC leq_nm) big_split_ord /=.
rewrite [X in op _ X]big1_seq => [|i _]; last first.
  rewrite big_hasC // ; apply/hasPn => x _.
  by rewrite -[X in _ < X]addn0 -addnA ltn_add2l ltn0.
rewrite Monoid.Theory.simpm /= -aux_triangular_index_bigop.
apply: eq_bigr => i _ ; rewrite subnKC //.
rewrite (eq_bigl (fun j => (i + (nat_of_ord j) < n) && ((nat_of_ord j) < n)))
                                                                    ; last first.
  move => j; symmetry.
  rewrite andb_idr //; apply: contraLR; rewrite -!leqNgt => leq_nj.
  by rewrite (leq_trans leq_nj) // leq_addl.
by rewrite big_ord_narrow_cond.
Qed.

End MoreBigop.


Section PolyCompl.

Lemma poly_cat (R : ringType) (p : {poly R}) n :
  Poly (take n p) + 'X^n * Poly (drop n p) = p.
Proof.
apply/polyP=> i; rewrite coefD coefXnM !coef_Poly; case: ltnP => Hi.
by rewrite nth_take // addr0.
rewrite nth_drop subnKC // [(take _ _)`_i]nth_default ?add0r //.
by rewrite size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

End PolyCompl.


Section TruncPolyDef.

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

End TruncPolyDef.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope ring_scope with trpoly_of.
Bind Scope ring_scope with trunc_polynomial.
Arguments trpoly {R} n%N.
Arguments trpoly_inj {R} [p1%R p2%R] : rename.
Notation "{ 'trpoly' R n }" :=  (trpoly_of n (Phant R)).

Hint Resolve size_trpoly.


Section CoefTruncPoly.

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

Fact trXn_subproof p : size (Poly (take n.+1 p)) <= n.+1.
Proof. by apply: (leq_trans (size_Poly _)); rewrite size_take geq_minl. Qed.
Definition trXn p := Trpoly_of (trXn_subproof p).

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

End CoefTruncPoly.

Local Open Scope trpoly_scope.

Notation "[ 'trpoly' s <= n => F ]" :=
  (trpoly_of_fun n (fun s => F)) : trpoly_scope.
Notation "[ 'trpoly' s => F ]" := [trpoly s <= _ => F] : trpoly_scope.
Notation "c %:S" := (trXn _ (c %:P)) (at level 2) : trpoly_scope.
Notation "\X" := (trXn _ 'X) : trpoly_scope.
Notation "\Xo( n )" := (trXn n 'X) (only parsing): trpoly_scope.


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


Section TruncPolyTheory.

Variable (R : ringType).
Implicit Types (p q r s : {poly R}).

Fact trXnC n a : trXn n a%:P = a%:P :> {poly R}.
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

Variable (n : nat).

Lemma coef_trpolyC (c : R) i :
  (c %:S : {trpoly R n})`_i = if i == 0%N then c else 0.
Proof. by rewrite trXnC coefC. Qed.

Lemma val_trpolyC (c : R) :
  val (c %:S : {trpoly R n}) = c %:P.
Proof. by apply/polyP => i /=; rewrite trXnE coef_trpolyC coefC. Qed.

Lemma trXnCE m a : trXn n (a%:S : {trpoly R m}) = a%:S.
Proof. by apply/trpolyP => i le_in; rewrite trXnC !coef_trpolyC. Qed.

Lemma trXn_mull p q : trXn n (val (trXn n p) * q) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans le_ji le_in).
Qed.

Lemma trXn_mulr p q : trXn n (p * val (trXn n q)) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans (leq_subr _ _) le_in).
Qed.

Lemma trXn_mul p q :
  trXn n (val (trXn n p) * val (trXn n q)) = trXn n (p * q).
Proof. by rewrite trXn_mulr trXn_mull. Qed.


(* zmodType structure *)
Implicit Types (f g : {trpoly R n}).

Fact zero_trpoly_subproof : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.
Definition zero_trpoly := Trpoly_of zero_trpoly_subproof.

Lemma add_trpoly_subproof f g :
  size (val f + val g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_trpoly. Qed.
Definition add_trpoly f g := Trpoly_of (add_trpoly_subproof f g).

Lemma opp_trpoly_subproof f : size (- val f) <= n.+1.
Proof. by rewrite size_opp ?size_trpoly. Qed.
Definition opp_trpoly f := Trpoly_of (opp_trpoly_subproof f).

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

Lemma trpolyC0 : (0 %:S : {trpoly R n}) = 0.
Proof. by apply/trpolyP => i _; rewrite coef_trpolyC if_same coef0. Qed.


(* ringType structure *)
Fact one_trpoly_proof : size (1 : {poly R}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.
Definition one_trpoly : {trpoly R n} := Trpoly_of one_trpoly_proof.

Definition mul_trpoly f g := trXn n (val f * val g).
Definition hmul_trpoly f g := [trpoly j <= n => f`_j * g`_j].
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

Lemma mul_trpoly_val f g : f * g = trXn n ((val f) * (val g)).
Proof. by []. Qed.

Lemma val_mul_trpoly f g : val (f * g) = trXn n ((val f) * (val g)).
Proof. by []. Qed.

Lemma exp_trpoly_val f (m : nat) : f ^+ m = trXn n ((val f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphX /= trpolyK -exprS.
Qed.

Lemma val_exp_trpoly f (m : nat) : val (f ^+ m) = trXn n ((val f) ^+ m).
Proof. by rewrite exp_trpoly_val. Qed.


(* lmodType structure *)
Lemma scale_trpoly_subproof (c : R) f : size (c *: val f) <= n.+1.
Proof. exact: leq_trans (size_scale_leq _ _) (size_trpoly _). Qed.
Definition scale_trpoly (c : R) f := Trpoly_of (scale_trpoly_subproof c f).

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

Fact trpolyC1 : 1 %:S = 1.
Proof. by apply/trpolyP => i _; rewrite trXnC. Qed.

Lemma trXnZ (c : R) (p : {poly R}) : trXn n (c *: p) =  c *: (trXn n p).
Proof. by rewrite linearZ. Qed.

Lemma alg_trpolyC (c : R) : c%:A = c%:S.
Proof. by apply/val_inj; rewrite val_trpolyC -alg_polyC. Qed.

(* Test *)
Example trpoly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Example trpoly1 : trXn n (1 : {poly R}) = 1.
Proof. by rewrite rmorph1. Qed.


Local Notation "f *h g" := (hmul_trpoly f g) (at level 2).

Lemma hmul_trpolyr1 f : f *h 1 = trXn n (f`_0)%:P.
Proof.
apply/trpolyP => i.
rewrite coef_trpolyC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_trpoly1r f : 1 *h f = trXn n (f`_0)%:P.
Proof.
apply/trpolyP => i.
rewrite coef_trpolyC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mul1r ?mul0r.
Qed.

Fact coef0_trpolyM f g : (f * g)`_0 = f`_0 * g`_0.
Proof. by rewrite coef_trXn coef0M. Qed.

Lemma trpoly_is_cst (g : {trpoly R 0}) : g = (g`_0) %:S.
Proof.
apply/val_inj => /=; have /= -> := trXnC 0 g`_0.
by apply: size1_polyC; rewrite size_trpoly.
Qed.

Lemma trpolyC_mul :
  {morph (fun x => (x%:S : {trpoly R n})) : a b / a * b >-> a * b}.
Proof. by move=> a b; apply val_inj; rewrite /= polyC_mul trXnE -trXn_mul. Qed.

End TruncPolyTheory.


Section TruncPolyX.

Variable (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Lemma trpoly0X m : m = 0%N -> \Xo(m) = 0 :> {trpoly R m}.
Proof.
by move=> ->; rewrite (trpoly_is_cst \X) coef_trXn coefX /= trpolyC0.
Qed.

Lemma val_trpolySX m : val (\Xo(m.+1)) = 'X%R :> {poly R}.
Proof.
apply/polyP => i.
by rewrite coef_trXn coefX; case: eqP => [->|] // _; rewrite if_same.
Qed.

Lemma val_trpolyX m : val (\Xo(m)) = (m != 0%N)%:R *: 'X%R :> {poly R}.
Proof.
case: m => [|m]; first by rewrite trpoly0X /= ?scale0r.
by rewrite val_trpolySX /= scale1r.
Qed.

Lemma trXn_trpolyX m : @trXn R n.+1 \Xo(m.+1) = \X.
Proof. by apply val_inj; rewrite !val_trpolySX. Qed.

Lemma commr_trpolyX f : GRing.comm f \X.
Proof.
apply/trpolyP => i le_in.
rewrite !mul_trpoly_val /= !trXnE trXn_mull trXn_mulr.
by rewrite !coef_trXn le_in commr_polyX.
Qed.

Lemma coef_trpolyMX f i :
  (\X * f)`_i = if i == 0%N then 0 else if i <= n then f`_i.-1 else 0.
Proof.
by rewrite !mul_trpoly_val /= !trXnE trXn_mull coef_trXn coefXM; case: i.
Qed.

End TruncPolyX.


Section ConverseTruncPoly.

Variable (R : ringType) (n : nat).

Fact size_conv_subproof (f : {trpoly R n}) :
  size (map_poly (fun c : R => c : R^c) f) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_trpoly. Qed.
Definition conv_trpoly f : {trpoly R^c n} := Trpoly_of (size_conv_subproof f).

Fact size_iconv_subproof (f : {trpoly R^c n}) :
  size (map_poly (fun c : R^c => c : R) f) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_trpoly. Qed.
Definition iconv_trpoly f : {trpoly R n} := Trpoly_of (size_iconv_subproof f).

Fact conv_trpoly_is_additive : additive conv_trpoly.
Proof.
by move=> f g; apply/trpolyP => i _; rewrite /= coefB !coef_map_id0 // coefB.
Qed.
Canonical conv_trpoly_additive := Additive conv_trpoly_is_additive.

Fact iconv_trpoly_is_additive : additive iconv_trpoly.
Proof.
by move=> f g; apply/trpolyP => i _; rewrite /= coefB !coef_map_id0 // coefB.
Qed.
Canonical iconv_trpoly_additive := Additive iconv_trpoly_is_additive.

Lemma conv_trpolyK : cancel conv_trpoly iconv_trpoly.
Proof. by move=> f; apply/trpolyP => i _; rewrite !coef_map_id0. Qed.
Lemma iconv_trpolyK : cancel iconv_trpoly conv_trpoly.
Proof. by move=> f; apply/trpolyP => i _; rewrite !coef_map_id0. Qed.

Lemma conv_trpoly1 : conv_trpoly 1 = 1.
Proof. by apply/trpolyP => i Hi; rewrite coef_map_id0 // !coef1. Qed.
Lemma iconv_trpoly1 : iconv_trpoly 1 = 1.
Proof. by apply/trpolyP => i Hi; rewrite coef_map_id0 // !coef1. Qed.

Lemma conv_trpolyM f g :
  conv_trpoly f * conv_trpoly g = conv_trpoly (g * f).
Proof.
apply/trpolyP => i Hi.
rewrite /conv_trpoly /= !trXnE coef_trXn Hi coef_map_id0 // coef_trXn Hi.
rewrite coefMr coefM; apply eq_bigr => j _ /=.
by rewrite !coef_map_id0.
Qed.
Lemma iconv_trpolyM f g :
  iconv_trpoly f * iconv_trpoly g = iconv_trpoly (g * f).
Proof.
apply/trpolyP => i Hi.
rewrite /conv_trpoly /= !trXnE coef_trXn Hi coef_map_id0 // coef_trXn Hi.
rewrite coefMr coefM; apply eq_bigr => j _ /=.
by rewrite !coef_map_id0.
Qed.

End ConverseTruncPoly.


Section TruncPolyTheoryComRing.

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

End TruncPolyTheoryComRing.


Section TruncPolyUnitRingLeft.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition unit_trpoly : pred {trpoly R n} := fun f => f`_0 \in GRing.unit.

Fixpoint inv_trpoly_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then inv_trpoly_rec f b m
    else - f`_(locked 0%N)^-1 *
           (\sum_(i < m) f`_(locked i.+1) * (inv_trpoly_rec f b (m - i.+1)%N))
  else f`_(locked 0%N)^-1.
Definition inv_trpoly f : {trpoly R n} :=
  if unit_trpoly f then [trpoly i <= n => inv_trpoly_rec f i i] else f.

Lemma coef0_inv_trpoly f : unit_trpoly f -> (inv_trpoly f)`_0 = f`_0^-1.
Proof. by rewrite /inv_trpoly => ->; rewrite coef_trpoly_of_fun /= -lock. Qed.

Lemma coefS_inv_trpoly f m :
  unit_trpoly f -> m < n ->
  (inv_trpoly f)`_m.+1 =
  - f`_(locked 0%N)^-1 *
    (\sum_(i < m.+1) f`_(locked i.+1) * (inv_trpoly f)`_(m - i)%N).
Proof.
move=> s_unit lt_mn.
rewrite /inv_trpoly s_unit coef_trpoly_of_fun /= ltnn lt_mn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => le_im _.
rewrite coef_trpoly_of_fun (leq_trans (leq_subr _ _) (ltnW lt_mn)); congr (_ * _).
rewrite /bump /= subSS.
move: (m - i)%N (leq_subr i m) {le_im} => {i} i le_im.
move: le_im => /subnKC <-; elim: (m - i)%N => [|k IHl]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_trpolyVr : {in unit_trpoly, right_inverse 1 inv_trpoly *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/trpolyP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  rewrite [0%N]lock /= coef_Poly nth_take -lock //.
  rewrite coefM big_ord_recr big_ord0 sub0n [0%N]lock /=.
  by rewrite /= add0r -lock coef0_inv_trpoly // mulrV // coefC.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/= [m.+1]lock /= coef_Poly.
case: (ltnP m.+1 n.+1) => Hmn.
  rewrite nth_take -lock //.
  rewrite coefM big_ord_recl [m.+1]lock [val ord0]/= subn0.
  rewrite -lock coefS_inv_trpoly //.
  rewrite mulNr mulrN -lock mulVKr // addrC.
  apply/eqP; rewrite subr_eq0; apply/eqP.
  by apply eq_bigr => [] [i] /=; rewrite -lock.
by rewrite nth_default // size_take -lock (leq_trans (geq_minl _ _)).
Qed.

Lemma inv_trpoly0id : {in [predC unit_trpoly], inv_trpoly =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_trpoly unfold_in /unit_trpoly => /negbTE ->.
Qed.

End TruncPolyUnitRingLeft.


Section TruncPolyTheoryUnitRing.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition invl_trpoly f := iconv_trpoly (inv_trpoly (conv_trpoly f)).

Lemma mul_trpolyVl : {in @unit_trpoly R n, left_inverse 1 invl_trpoly *%R}.
Proof.
move=> f Hf; rewrite /invl_trpoly -{2}(conv_trpolyK f).
rewrite iconv_trpolyM mul_trpolyVr ?iconv_trpoly1 //.
by move: Hf; rewrite !unfold_in coef_map_id0.
Qed.

(* General semi-group theory : left inverse = right inverse *)
Lemma invr_trpolyE f : unit_trpoly f -> inv_trpoly f = invl_trpoly f.
Proof.
move=> H; have:= erefl (invl_trpoly f * f * inv_trpoly f).
by rewrite -{2}mulrA mul_trpolyVl // mul1r mul_trpolyVr // mulr1.
Qed.

Lemma mul_trpolyrV :
  {in @unit_trpoly R n, left_inverse 1 (@inv_trpoly R n) *%R}.
Proof. by move=> f Hs; rewrite invr_trpolyE // mul_trpolyVl. Qed.

Lemma unit_trpolyP f g : g * f = 1 /\ f * g = 1 -> unit_trpoly f.
Proof.
move=> [] /(congr1 val)/(congr1 (coefp (locked 0%N))) /=.
rewrite coef_Poly nth_take -lock // coef1 coef0M eq_refl => Hl.
move=>    /(congr1 val)/(congr1 (coefp (locked 0%N))) /=.
rewrite coef_Poly nth_take -lock // coef1 coef0M eq_refl => Hr.
by rewrite /unit_trpoly; apply/unitrP; exists g`_0.
Qed.

Definition trpoly_unitMixin :=
  UnitRingMixin mul_trpolyrV (@mul_trpolyVr _ _) unit_trpolyP (@inv_trpoly0id _ _).
Canonical trpoly_unitRingType :=
  Eval hnf in UnitRingType {trpoly R n} trpoly_unitMixin.

Lemma coefsV0 f : unit_trpoly f -> f^-1`_0 = f`_0^-1.
Proof. exact: coef0_inv_trpoly. Qed.

Lemma unit_trpolyE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma trXn_unitE (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_trpolyE nth0_trXn. Qed.

Lemma coef_inv_trpoly f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_j.+1 * f^-1`_(i - j.+1)).
Proof.
move=> funit; case: ltnP => Hi.
  by rewrite -(trpolyK f^-1) coef_trXn leqNgt Hi.
case: i Hi => [|i] Hi; first by rewrite eq_refl coefsV0.
have -> : f^-1 = inv_trpoly f by [].
rewrite coefS_inv_trpoly // -!lock; congr (_ * _).
by apply eq_bigr => /= j _; rewrite -lock subSS.
Qed.

Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
case (boolP (f \is a GRing.unit))=> [f_unit|]; first by rewrite coef_inv_trpoly.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite unit_trpolyE => /invr_out ->.
Qed.

Lemma trpolyC_inv (c : R) : (trXn n c%:P)^-1 = trXn n (c^-1)%:P.
Proof.
case (boolP (c \in GRing.unit)) => [Uc | nUc].
  by rewrite -/((trXn n \o @polyC R) _) -rmorphV.
by rewrite !invr_out // unit_trpolyE coef_trXn coefC.
Qed.

End TruncPolyTheoryUnitRing.

Lemma trXnV (R : unitRingType) n m (f : {trpoly R m}) :
  n <= m -> trXn n (f^-1) = (trXn n f) ^-1.
Proof.
move=> leq_mn.
case (boolP (f`_0 \is a GRing.unit)) => f0U; first last.
  by rewrite !invr_out // unit_trpolyE ?nth0_trXn.
apply: (@mulrI _ (trXn _ f)); rewrite ?divrr ?(unit_trpolyE, nth0_trXn) //.
rewrite -!rmorphM /= -(trXn_trXn _ leq_mn) -val_mul_trpoly.
by rewrite divrr ?unit_trpolyE // trXn1.
Qed.


Section TruncPolyTheoryComUnitRing.

Variable (R : comUnitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Canonical trpoly_comUnitRingType := [comUnitRingType of {trpoly R n}].
Canonical trpoly_unitAlgType := Eval hnf in [unitAlgType R of {trpoly R n}].

End TruncPolyTheoryComUnitRing.


Section TruncPolyTheoryIDomain.

Variable R : idomainType.

Lemma poly_modXn n (p : {poly R}) : p %% 'X^n = Poly (take n p).
Proof.
rewrite -{1}(poly_cat p n) addrC mulrC Pdiv.IdomainUnit.modp_addl_mul_small //.
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

Fact mod_trpoly (m : nat) f : n <= m -> f %% 'X^m.+1 = f.
Proof.
move=> leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_trpoly _)).
Qed.

End TruncPolyTheoryIDomain.


Section MapTruncPoly.

Variables (K L : ringType) (n : nat) (f : {rmorphism K -> L}).

Implicit Type g h : {trpoly K n}.

Fact map_trpoly_subproof g : size (map_poly f (val g)) <= n.+1.
Proof.
by rewrite map_polyE (leq_trans (size_Poly _)) // size_map size_trpoly.
Qed.
Definition map_trpoly g := Trpoly_of (map_trpoly_subproof g).

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

(* Tests *)
Fact test_map_trpoly0 : map_trpoly 0 = 0.
Proof. by rewrite linear0. Qed.

Fact test_map_trpolyD g h :
  map_trpoly (g + h) = (map_trpoly g) + (map_trpoly h).
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

End MapTruncPoly.

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


Section Coefficient01.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition coef0_is_0 : pred_class := fun f : {trpoly R n} => f`_0 == 0.
Definition coef0_is_1 : pred_class := fun f : {trpoly R n} => f`_0 == 1.

Lemma coef0_is_0E f : (f \in coef0_is_0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Lemma coef0_is_1E f : (f \in coef0_is_1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Fact c0_is_0_idealr : idealr_closed coef0_is_0.
Proof.
split => [|| a p q ]; rewrite ?coef0_is_0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefD q0_eq0 addr0 coef0_trpolyM p0_eq0 mulr0.
Qed.

Fact c0_is_0_key : pred_key coef0_is_0. Proof. by []. Qed.

Canonical c0_is_0_keyed := KeyedPred c0_is_0_key.
Canonical c0_is_0_opprPred := OpprPred c0_is_0_idealr.
Canonical c0_is_0_addrPred := AddrPred c0_is_0_idealr.
Canonical c0_is_0_zmodPred := ZmodPred c0_is_0_idealr.

Definition c0_is_0_ntideal := idealr_closed_nontrivial c0_is_0_idealr.
Canonical c0_is_0_ideal := MkIdeal c0_is_0_zmodPred c0_is_0_ntideal.

Lemma coef0_is_0Z f c : f \in coef0_is_0 -> c *: f \in coef0_is_0.
Proof. by move=> hf; rewrite -mulr_algl idealMr. Qed.

Lemma coef0_is_0X f i : f \in coef0_is_0 -> f ^+ i.+1 \in coef0_is_0.
Proof. by move=> hf; rewrite exprSr idealMr. Qed.

Lemma coef0_is_10 f : (f \in coef0_is_1) = ((1 - f) \in coef0_is_0).
Proof. by rewrite ?coef0_is_0E ?coef0_is_1E coefB coef1 subr_eq0 eq_sym. Qed.

Lemma coef0_is_01 f : (f \in coef0_is_0) = ((1 + f) \in coef0_is_1).
Proof. by rewrite coef0_is_10 -[RHS]rpredN !opprD !opprK addKr. Qed.

Lemma coef0_is_1_add01 f g :
  f \in coef0_is_0 -> g \in coef0_is_1 -> f + g \in coef0_is_1.
Proof.
rewrite coef0_is_0E !coef0_is_1E coefD => /eqP -> /eqP ->.
by rewrite add0r.
Qed.

Lemma trpolyX_in_coef0_is_0 : \X \in coef0_is_0.
Proof. by rewrite coef0_is_0E coef_trXn coefX. Qed.

(* tests *)
Example zero_in_coef0_is_0 : 0 \in coef0_is_0.
Proof. by rewrite rpred0. Qed.

Example coef0_is_0D f g :
    f \in coef0_is_0 -> g \in coef0_is_0 -> f + g \in coef0_is_0.
Proof. by move=> hf hg; rewrite rpredD. Qed.

Example coef0_is_0N f : f \in coef0_is_0 -> (-f) \in coef0_is_0.
Proof. by move=> hf; rewrite rpredN. Qed.


Fact mulr_closed_c0_is_1 : mulr_closed coef0_is_1.
Proof.
split=> [|x y]; rewrite !coef0_is_1E ?coefC //.
by rewrite coef0_trpolyM; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.
Fact c0_is_1_key : pred_key coef0_is_1. Proof. by []. Qed.
Canonical c0_is_1_keyed := KeyedPred c0_is_1_key.
Canonical c0_is_1_MulrPred := MulrPred mulr_closed_c0_is_1.

(* Tests *)
Example one_in_coef0_is_1 : 1 \in coef0_is_1.
Proof. by rewrite rpred1. Qed.

Example coef0_is_1M f g :
  f \in coef0_is_1 -> g \in coef0_is_1 -> f * g \in coef0_is_1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

End Coefficient01.
Arguments coef0_is_0 {R n}.
Arguments coef0_is_1 {R n}.

Lemma coef0_is_0_trXn (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
  (trXn m f \in coef0_is_0) = (f \in coef0_is_0).
Proof. by rewrite !coef0_is_0E nth0_trXn. Qed.

Lemma coef0_is_1_trXn (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
  (trXn m f \in coef0_is_1) = (f \in coef0_is_1).
Proof. by rewrite !coef0_is_1E nth0_trXn. Qed.


Section Coefficient01Unit.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact invr_closed_c0_is_1 : invr_closed (@coef0_is_1 R n).
Proof.
move=> f; rewrite !coef0_is_1E nth0_inv; move/eqP ->.
by rewrite invr1.
Qed.
Canonical c0_is_1_DivrPred := DivrPred invr_closed_c0_is_1.

Example coef0_is_1V f : f \in coef0_is_1 -> f^-1 \in coef0_is_1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Example coef0_is_1_div f g :
  f \in coef0_is_1 -> g \in coef0_is_1 -> f / g \in coef0_is_1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.

Lemma coef0_is_1_unit f : f \in coef0_is_1 -> f \is a GRing.unit.
Proof. by rewrite !coef0_is_1E unit_trpolyE => /eqP ->; apply unitr1. Qed.

End Coefficient01Unit.


Section Coefficient01IDomain.

Variables (R : idomainType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact c0_is_0_prime : prime_idealr_closed (@coef0_is_0 R n).
Proof.
by move => x y; rewrite -!topredE /= /coef0_is_0 coef0_trpolyM mulf_eq0.
Qed.
Canonical coef0_is_0_pideal := MkPrimeIdeal (c0_is_0_ideal R n) c0_is_0_prime.

Example coef0_is_0_prime_test f g :
  f * g \in coef0_is_0 -> (f \in coef0_is_0) || (g \in coef0_is_0).
Proof. by rewrite prime_idealrM. Qed.

End Coefficient01IDomain.


Section DivisionByX.

Definition divfX (R : ringType) m (f : {trpoly R m}) :=
  [trpoly i <= m.-1 => f`_i.+1].

Variable K : idomainType.

Lemma divfXE (m : nat) :
  {in @coef0_is_0 K m, forall f, divfX f = trXn m.-1 (f %/ 'X)}.
Proof.
move=> f.
move/eqP/polyXP; rewrite Pdiv.IdomainUnit.dvdp_eq ?lead_coefX ?unitr1 //.
rewrite /divfX; move/eqP => h.
rewrite [in LHS]h; apply/trpolyP => i Hi.
by rewrite coef_poly coef_trXn ltnS Hi coefMX.
Qed.

End DivisionByX.

Lemma map_trpoly_divfX (K L : ringType) (f : {rmorphism K -> L})
  (m : nat) (g : {trpoly K m}) :
  map_trpoly f (divfX g) = divfX (map_trpoly f g).
Proof.
apply/trpolyP => i lt_im1.
by rewrite !(coef_trpoly_of_fun, coef_map, lt_im1).
Qed.


Section Derivative.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Lemma deriv_trXn (p : {poly R}) : (trXn n.+1 p)^`() = trXn n (p ^`()).
Proof.
apply/polyP => i /=.
rewrite coef_deriv !trXnE !coef_trXn coef_deriv ltnS.
by case: leqP => //; rewrite mul0rn.
Qed.

Fact trXn_deriv_trpoly (m : nat) (f : {trpoly R n}) : n <= m ->
  trXn m (val f)^`() = (val f)^`() :> {poly R}.
Proof.
move => le_nm; apply/polyP => i /=.
rewrite coef_deriv !trXnE !coef_trXn coef_deriv.
case: leqP => lt_mi //.
by rewrite coef_trpoly ltnNge (ltnW (leq_ltn_trans le_nm lt_mi)) /= mul0rn.
Qed.

Definition deriv_trpoly f := [trpoly j <= n.-1 => f`_j.+1 *+ j.+1].
Local Notation "f ^` () " := (deriv_trpoly f) : trpoly_scope.

Lemma coef_deriv_trpoly f j :
  (deriv_trpoly f)`_j = f`_j.+1 *+ j.+1.
Proof.
rewrite coef_trpoly_of_fun; case: leqP => //.
rewrite coef_trpoly [j < n]ltnNge.
by case: n f => /= [|m f ->]; rewrite mul0rn.
Qed.

Lemma val_deriv_trpoly f : val (deriv_trpoly f) = (val f)^`()%R.
Proof. by apply/polyP => i; rewrite coef_deriv_trpoly coef_deriv. Qed.

Lemma deriv_trpolyE f : deriv_trpoly f = trXn n.-1 (val f)^`().
Proof. by rewrite -val_deriv_trpoly trpolyK. Qed.

Fact deriv_trpoly0 : (0 : {trpoly R n}) ^`() = 0.
Proof. by apply val_inj; rewrite val_deriv_trpoly deriv0. Qed.

Lemma deriv_trpolyC (c : R) : c %:S ^`() = 0 :> {trpoly _ n.-1}.
Proof. by apply val_inj; rewrite val_deriv_trpoly val_trpolyC derivC. Qed.

Lemma deriv_trpoly1 : 1 ^`() = 0 :> {trpoly _ n.-1}.
Proof. by rewrite -trpolyC1 deriv_trpolyC. Qed.

Fact deriv_trpolyD f g : (f + g)^`() = f^`()%trpoly + g^`()%trpoly.
Proof.
apply/trpolyP => i le_in1.
by rewrite coefD !coef_poly ltnS le_in1 coefD -mulrnDl.
Qed.

Fact deriv_trpolyZ (c : R) f : (c *: f) ^`() = c *: f ^`()%trpoly.
Proof.
apply/trpolyP => i le_in1.
by rewrite !(coef_poly, coefZ) ltnS le_in1 mulrnAr.
Qed.

Fact deriv_trpoly_is_linear : linear deriv_trpoly.
Proof. by move => c f g; rewrite deriv_trpolyD deriv_trpolyZ. Qed.
Canonical deriv_trpoly_additive := Additive deriv_trpoly_is_linear.
Canonical deriv_trpoly_linear := Linear deriv_trpoly_is_linear.

(* Tests *)
Example test_deriv_trpoly0 : 0 ^`() = 0 :> {trpoly R n.-1}.
Proof. by rewrite linear0. Qed.

Example test_deriv_trpolyD f g :
  (f + g)^`() = f^`()%trpoly + g^`()%trpoly.
Proof. by rewrite linearD. Qed.

End Derivative.

Notation "f ^` () " := (deriv_trpoly f) : trpoly_scope.


Section MoreDerivative.

Variables (R : ringType).

Lemma deriv_trpoly0p (f : {trpoly R 0}) : f ^`() = 0.
Proof. by rewrite [f]trpoly_is_cst deriv_trpolyC. Qed.

Theorem deriv_trpolyM n (f g : {trpoly R n}) :
  (f * g) ^`() = f ^`()%trpoly * (trXn n.-1 g) + (trXn n.-1 f) * g ^`()%trpoly.
Proof.
move: f g; case: n => /= [f g | m f g].
  rewrite [f]trpoly_is_cst [g]trpoly_is_cst -trpolyC_mul !deriv_trpolyC.
  by rewrite mul0r mulr0 addr0.
apply/val_inj; rewrite !deriv_trpolyE /=.
by rewrite !trXnE !trXn_mul deriv_trXn trXn_trXn // derivM rmorphD.
Qed.

End MoreDerivative.


Section DerivativeUnitRing.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

(* Noncommutative version *)
Theorem deriv_trpolyV_unit f :
  f \is a GRing.unit ->
  (f ^-1) ^`() = - trXn n.-1 (f ^-1) * (f ^`()%trpoly) * trXn n.-1 (f ^-1).
Proof.
move => fU.
have:= erefl (f / f); rewrite {2}divrr //.
move/(congr1 (@deriv_trpoly R n)).
rewrite deriv_trpolyM -trpolyC1 deriv_trpolyC.
move/eqP; rewrite addrC; set X := (X in X + _); rewrite (addr_eq0 X _) {}/X.
move/eqP/(congr1 (fun x => (trXn n.-1 f ^-1) * x)).
rewrite {1}trXnV ?leq_pred // mulKr ?(mulrN, mulNr, mulrA) //.
by rewrite unit_trpolyE nth0_trXn.
Qed.

End DerivativeUnitRing.


Section DerivativeComUnitRing.

Variables (R : comUnitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Theorem deriv_trpolyV f :
  f \is a GRing.unit ->
  (f ^-1) ^`() = - (f ^`()%trpoly) / trXn n.-1 (f ^+ 2).
Proof.
move=> fU.
rewrite deriv_trpolyV_unit // -mulrA mulrC -mulrA !mulrN mulNr.
rewrite trXnV ?leq_pred // -invrM ?unit_trpolyE ?nth0_trXn //.
by rewrite -{1}rmorphM expr2 /= trXnE trXn_trXn ?leq_pred.
Qed.

Theorem deriv_div_trpoly f g :
  g \is a GRing.unit ->
  (f / g) ^`() = (f^`()%trpoly * trXn n.-1 g - trXn n.-1 f * g ^`()%trpoly)
                                                    / (trXn n.-1 (g ^+ 2)).
Proof.
move => fU.
rewrite deriv_trpolyM deriv_trpolyV // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
rewrite trXnV ?leq_pred // expr2 ?leq_pred //.
have -> : trXn n.-1 (g * g) = trXn n.-1 ((val g) * g).
  by apply/val_inj => /=; rewrite !trXnE trXn_trXn ?leq_pred.
rewrite rmorphM /= invrM ?trXn_unitE ?nth_trXn //.
by rewrite mulrA divrr ?trXn_unitE ?nth_trXn // mul1r.
Qed.

End DerivativeComUnitRing.


Section Primitive.

Variables (R : unitRingType) (n : nat).

Definition prim (p : {poly R}) :=
    \poly_(i < (size p).+1) (p`_i.-1 *+ (i != 0%N) / (i%:R)).

Local Notation "\int p" := (prim p) (at level 2).

Lemma coef_prim (p : {poly R}) (i : nat) :
                        (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [| i]; first by rewrite eqxx coef_poly invr0 mulr0.
rewrite succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => //; rewrite mul0r.
Qed.

Lemma coef0_prim (p : {poly R}) : (\int p)`_0 = 0.
Proof. by rewrite coef_prim eqxx. Qed.

Lemma primC (c : R) : \int (c%:P) = c *: 'X.
Proof.
apply/polyP => i.
rewrite /prim /prim coef_poly size_polyC -[c *: 'X]coefK.
have [-> | c_neq0 ] := eqVneq c 0.
  rewrite eqxx /= scale0r size_poly0 coef_poly ltn0; case: i => [|i].
    by rewrite invr0 mulr0.
    by rewrite coefC.
rewrite c_neq0 /= coef_poly coefZ coefX.
have -> : size (c *: 'X) = 2%N.
  rewrite -mulr_algl alg_polyC size_Mmonic ?monicX ?polyC_eq0 //.
  by rewrite size_polyX size_polyC c_neq0.
congr if_expr; case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite coefC mulr1n.
case: i => [|i]; first by rewrite !eqxx invr1.
by rewrite /= mul0r mulr0.
Qed.

Lemma primX : \int 'X = (2%:R) ^-1 *: 'X ^+2.
Proof.
rewrite /prim /prim size_polyX ; apply/polyP => i.
rewrite coef_poly coefZ coefXn coefX.
case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite eqn0Ngt ltn0Sn /=; case: i => [ | i ] ; first by rewrite mul0r mulr0.
case: i => [|i]; first by rewrite mul1r mulr1.
by rewrite mulr0.
Qed.

Lemma primXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
Proof.
rewrite /prim /prim size_polyXn ; apply/polyP => i.
rewrite coefZ !coefXn coef_poly !coefXn.
have [-> | /negbTE i_neq_Sm ] := eqVneq i m.+1.
  by rewrite eqxx ltnSn mulr1 eqxx mul1r.
rewrite i_neq_Sm /= mulr0 ; case: (i < m.+2) => [] //.
have [ -> | /negbTE i_neq0 ] := eqVneq i 0%N; first by rewrite eqxx invr0 mulr0.
rewrite i_neq0 ; move/negbT : i_neq0 ; move/negbT : i_neq_Sm.
case: i => [ // | i ].
by rewrite (inj_eq succn_inj) => /negbTE -> _ ; rewrite mul0r.
Qed.

Fact prim_is_linear : linear prim.
Proof.
move => k p q ; apply/polyP => i.
case: i => [ | i]; first by rewrite coefD coefZ !coef0_prim mulr0 addr0.
by rewrite !(coef_prim, coefD, coefZ) mulrDl -mulrA.
Qed.
Canonical prim_additive := Additive prim_is_linear.
Canonical prim_linear := Linear prim_is_linear.

(* tests *)
Fact prim0 : prim 0 = 0.
Proof. exact: linear0. Qed.

Fact primD : {morph prim : p q / p + q}.
Proof. exact: linearD. Qed.

Fact primN : {morph prim : p / - p}.
Proof. exact: linearN. Qed.

Fact primB : {morph prim : p q / p - q}.
Proof. exact: linearB. Qed.


Implicit Types (f g : {trpoly R n}).

Lemma size_prim_leq f : size (prim f) <= n.+2.
Proof. by apply: (leq_trans (size_poly _ _) _); rewrite ltnS. Qed.
Definition prim_trpoly f := Trpoly_of (size_prim_leq f).

Lemma coef_prim_trpoly f i : (prim_trpoly f)`_i = (prim f)`_i.
Proof. by []. Qed.

Fact prim_trpoly_is_linear : linear prim_trpoly.
Proof.
move=> k p q; apply/trpolyP => i lt_in1.
rewrite coefD coefZ !coef_prim.
case: i lt_in1 => [|i]/=; first by rewrite mulr0 addr0.
rewrite ltnS => lt_in.
by rewrite coefD coefZ mulrDl mulrA.
Qed.
Canonical prim_trpoly_linear := Linear prim_trpoly_is_linear.

(* tests *)
Example prim_trpoly0 : prim_trpoly 0 = 0.
Proof. exact: linear0. Qed.

Example prim_trpolyD : {morph prim_trpoly : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma coef0_prim_trpoly f : (prim_trpoly f)`_0 = 0.
Proof. by rewrite coef_poly eqxx mulr0n invr0 mulr0. Qed.

End Primitive.


Section MoreExpPoly.

Variable (R : ringType).
Implicit Type (p q : {poly R}).

Lemma coefX_eq0 n m p :
  p`_0 = 0 -> n < m -> (p ^+ m)`_n = 0.
Proof.
elim: m n p => [|m IHm] n p Hp; first by rewrite ltn0.
case: n => [_|n].
  suff -> : (p ^+ m.+1)`_0 = (p`_0) ^+ m.+1 by rewrite Hp expr0n.
  elim: m.+1 {IHm} => {m}[|m IHm]; first by rewrite !expr0 coef1 eq_refl.
  by rewrite !exprS -{}IHm coefM big_ord_recl big_ord0 addr0.
rewrite ltnS exprS => lt_nm.
rewrite coefM; apply big1 => [] [j]; rewrite /= ltnS => le_ji _.
case: j le_ji => [|j]; first by rewrite Hp mul0r.
rewrite !ltnS subSS => le_jn.
by rewrite IHm ?mulr0 // (leq_ltn_trans (leq_subr _ _ ) lt_nm).
Qed.

Lemma trXn_eq0 n m p :
  p`_0 = 0 -> n < m -> trXn n (p ^+ m) = 0.
Proof.
move=> H1 H2.
apply/trpolyP => i le_in; rewrite coef_trXn coef0 le_in.
by rewrite coefX_eq0 // (leq_ltn_trans le_in H2).
Qed.

Lemma trXnMX_eq0 n p q i j :
  p`_0 = 0 -> q`_0 = 0 -> n < i + j -> trXn n (p ^+ i * q ^+ j) = 0.
Proof.
move=> p0 q0 lt_n_addij.
apply/trpolyP => l le_li; rewrite coef0.
rewrite coef_trXn le_li coefM.
rewrite (bigID (fun k => val k >= i)) /= ?big1 ?addr0 // => [] [k Hk] /= H.
- rewrite -ltnNge in H.
  by rewrite coefX_eq0 ?mul0r.
- rewrite ltnS in Hk.
  rewrite [X in _* X]coefX_eq0 ?mulr0 //.
  rewrite leq_ltn_subLR //.
  exact: (leq_ltn_trans le_li (leq_trans lt_n_addij (leq_add _ _))).
Qed.

Lemma expr_coef0_is_0 (n m : nat) :
  n < m -> {in @coef0_is_0 R n, forall f, f ^+ m = 0}.
Proof.
move => lt_mn f; rewrite coef0_is_0E; move/eqP.
move/trXn_eq0/(_ lt_mn) => <-.
by rewrite rmorphX /= trpolyK.
Qed.

End MoreExpPoly.

Section MoreCompPoly.

Variable (R : comRingType).
Implicit Type (p q : {poly R}).

Lemma trXn_comp_polyr n p q : trXn n (p \Po q) = trXn n (p \Po trXn n q).
Proof.
apply/trXnP => i le_in.
rewrite !coef_comp_poly; apply eq_bigr => j _; congr (_ * _).
have /= := (congr1 (fun x => (trpoly _ x)`_i) (exp_trpoly_val (trXn n q) j)).
rewrite !coef_trXn le_in => <-.
by rewrite -rmorphX /= trXnE coef_trXn le_in.
Qed.

Lemma trXn_comp_polyl n p q :
  q`_0 = 0 -> trXn n (p \Po q) = trXn n ((trXn n p) \Po q).
Proof.
move => q0_eq0; apply/trXnP => i le_in.
rewrite -{1}(poly_cat p n.+1) comp_polyD coefD comp_polyM !trXnE.
rewrite rmorphX /= comp_polyX [X in _ + X](_ : _ = 0) ?addr0 //.
rewrite coefM; apply big1 => [] [j /=]; rewrite ltnS => le_ji _.
by rewrite coefX_eq0 ?mul0r // ltnS (leq_trans le_ji le_in).
Qed.

Lemma coef_comp_poly_cX p c i : (p \Po (c *: 'X))`_i = c ^+ i * p`_i.
Proof.
rewrite coef_comp_poly.
rewrite (eq_bigr (fun j : 'I_ _ =>
                    c ^+ j * p`_j * (i == j)%:R)) => [|j _]; first last.
  rewrite -mulr_algl exprMn_comm; last exact: commr_polyX.
  by rewrite -in_algE -rmorphX mulr_algl coefZ coefXn mulrA [p`_j * _]mulrC.
case: (ltnP i (size p)) => [lt_isz | le_szi].
- rewrite (bigD1 (Ordinal lt_isz)) //= big1 ?addr0; first last.
    move=> [j /= lt_jsz]; rewrite -val_eqE /= eq_sym => /negbTE ->.
    by rewrite mulr0.
  by rewrite eqxx mulr1.
- rewrite nth_default // mulr0 big1 // => [] [j /= lt_jsz] _.
  by rewrite (gtn_eqF (leq_trans lt_jsz le_szi)) mulr0.
Qed.

End MoreCompPoly.


Section Composition.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}) (p q : {poly R}).

Definition comp_trpoly m (f g : {trpoly R m}) :=
  if f \in coef0_is_0
  then trXn m (comp_poly f g)
  else (g`_0%N)%:S.  (* avoid particular cases (e.g. associatvity) *)

Local Notation "f \So g" := (comp_trpoly g f) : trpoly_scope.


Lemma comp_trpoly_coef0_neq0 f g :
  g \notin coef0_is_0 -> f \So g = (f`_0%N)%:S.
Proof. by move/negbTE => p0_neq0; rewrite /comp_trpoly p0_neq0. Qed.

Lemma comp_trpoly_coef0_eq0 f g :
  g \in coef0_is_0 -> f \So g = trXn n (f \Po g).
Proof. by move => f0_eq0 ; rewrite /comp_trpoly f0_eq0. Qed.

Lemma coef0_comp_trpoly f g : (f \So g)`_0 = f`_0.
Proof.
rewrite /comp_trpoly; case: (boolP (_ \in _)); last by rewrite coef_trpolyC.
rewrite coef0_is_0E coef_trXn {-2}[0%N]lock /= -lock => /eqP.
by rewrite -!horner_coef0 horner_comp => ->.
Qed.

Lemma coef0_is_0_comp f g : (f \So g \in coef0_is_0) = (f \in coef0_is_0).
Proof. by rewrite !coef0_is_0E coef0_comp_trpoly. Qed.

Lemma coef0_is_1_comp f g : (f \So g \in coef0_is_1) = (f \in coef0_is_1).
Proof. by rewrite !coef0_is_1E coef0_comp_trpoly. Qed.


Section Variable_f.

Variable (f : {trpoly R n}).

Lemma comp_trpoly0r : f \So 0 = (f`_0) %:S.
Proof. by rewrite comp_trpoly_coef0_eq0 ?rpred0 // comp_poly0r. Qed.

Lemma comp_trpoly0 : 0 \So f = 0.
Proof.
case (boolP (f \in coef0_is_0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_trpoly_coef0_eq0 // comp_poly0 rmorph0.
- by rewrite comp_trpoly_coef0_neq0 // coef0 trpolyC0.
Qed.

Lemma comp_trpolyC (c : R) : c%:S \So f = c%:S.
Proof.
case (boolP (f \in coef0_is_0)) => [f0_eq0 | f0_neq0].
- rewrite comp_trpoly_coef0_eq0 //=; have /= -> := trXnC n c.
  by rewrite comp_polyC.
- by rewrite comp_trpoly_coef0_neq0 ?coef_trpolyC.
Qed.

Lemma comp_trpolyCf (c : R) : f \So (c%:S) = (f`_0)%:S.
Proof.
have [->| /negbTE c_neq0] := eqVneq c 0.
  by rewrite trpolyC0 comp_trpoly0r.
rewrite comp_trpoly_coef0_neq0 //.
by rewrite coef0_is_0E nth0_trXn coefC eqxx negbT.
Qed.

Hypothesis (f0_is_0 : f \in coef0_is_0).

Fact comp_trpoly_is_additive : additive (comp_trpoly f).
Proof.
move => u v; rewrite !comp_trpoly_coef0_eq0 //.
by apply/val_inj; rewrite !rmorphB.
Qed.

Fact comp_trpoly_is_linear : linear (comp_trpoly f).
Proof.
move => a q r.
by rewrite !comp_trpoly_coef0_eq0 // !rmorphD /= !linearZ.
Qed.

End Variable_f.


Lemma comp_trpolyXr f : n != 0%N -> f \So \X = f.
Proof.
rewrite comp_trpoly_coef0_eq0 ?trpolyX_in_coef0_is_0 //.
case: n f => // m f _.
by rewrite val_trpolySX comp_polyXr trpolyK.
Qed.

Lemma comp_trpolyX : n != 0%N -> {in coef0_is_0, forall f, \X \So f = f}.
Proof.
move=> Hn f /comp_trpoly_coef0_eq0 ->.
case: n f Hn => // m f _.
by rewrite val_trpolySX comp_polyX trpolyK.
Qed.

Lemma coef_comp_trpoly_cX f c i :
  n != 0%N -> (f \So (c *: \X))`_i = c ^+ i * f`_i.
Proof.
move=> n_neq0.
case: (leqP i n) => [le_in | lt_ni]; first last.
  rewrite coef_trpoly leqNgt lt_ni /= nth_default ?mulr0 //.
  exact: (leq_trans (size_trpoly f) lt_ni).
rewrite -coef_comp_poly_cX.
rewrite comp_trpoly_coef0_eq0 ?coef0_is_0Z ?trpolyX_in_coef0_is_0 //.
by rewrite coef_trXn le_in /= trXnE val_trpolyX n_neq0 scale1r.
Qed.

Lemma comp_trpolyA f g h : f \So (g \So h) = (f \So g) \So h.
Proof.
case (boolP (h \in coef0_is_0)) => [h0_eq0 | h0_neq0]; first last.
  rewrite !(comp_trpoly_coef0_neq0 _ h0_neq0).
  by rewrite comp_trpolyCf coef0_comp_trpoly.
case (boolP (g \in coef0_is_0)) => [g0_eq0 | g0_neq0]; first last.
  by rewrite !(comp_trpoly_coef0_neq0 f) ?comp_trpolyC // coef0_is_0_comp.
rewrite comp_trpoly_coef0_eq0 ?coef0_is_0_comp //.
rewrite !comp_trpoly_coef0_eq0 //.
rewrite -trXn_comp_polyr comp_polyA trXn_comp_polyl //.
by move: h0_eq0; rewrite coef0_is_0E => /eqP.
Qed.

End Composition.

Notation "f \So g" := (comp_trpoly g f) : trpoly_scope.


Section MoreComposition.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).


Theorem deriv_trpoly_comp f g :
  f \in coef0_is_0 ->
  (g \So f)^`() = (g ^`()%trpoly \So (trXn n.-1 f)) * f^`()%trpoly.
Proof.
rewrite !deriv_trpolyE //.
move: f g; case: n => [|m] f g f0_eq0.
  rewrite [f]trpoly_is_cst [g]trpoly_is_cst !trXn_trXn // comp_trpolyC.
  by rewrite !val_trpolyC !derivC trXn0 mulr0.
rewrite /= !comp_trpoly_coef0_eq0 ?coef0_is_0_trXn //.
apply/val_inj.
rewrite deriv_trXn deriv_comp trXn_trXn //= !trXnE trXn_mulr -trXn_mull.
congr (val (trXn _ (_ * _))).
rewrite -val_deriv_trpoly trpolyK.
rewrite !comp_polyE !linear_sum /= !linear_sum; apply: eq_bigr => [] [i /=] _ _.
rewrite !trXnE !linearZ /=; congr (_ *: _).
by rewrite !trXnE !rmorphX /= trXnE trXn_trXn.
Qed.

End MoreComposition.


Section ExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition exp f : {trpoly R n} :=
  if f \notin coef0_is_0 then 0 else
  trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i).

Definition log f : {trpoly R n} :=
  if f \notin coef0_is_1 then 0 else
  trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i).

Definition expr_trpoly (c : R) f := exp (c *: log f).

Lemma exp_coef0_is_0 f : f \in coef0_is_0 ->
  exp f = trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i).
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_is_0_val f : f \in coef0_is_0 ->
  exp f = trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (val f) ^+i).
Proof.
rewrite /exp => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite !linearZ /= val_exp_trpoly trXn_trXn.
Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_is_0 -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0 : exp (0 : {trpoly R n}) = 1.
Proof.
apply/trpolyP => i le_in.
rewrite exp_coef0_is_0 ?rpred0 // !raddf_sum /=.
rewrite big_ord_recl /= fact0 invr1 alg_polyC trXnE trXn1.
rewrite coefD /= coef_sum big1 ?addr0 // => [] [j ] _ _ /=.
by rewrite /bump /= add1n expr0n /= scaler0 trXnE trXn0 coef0.
Qed.

Lemma expC (c : R) : exp (c %:S) = (c == 0)%:R %:S :> {trpoly R n}.
Proof.
case (boolP (c %:S \in @coef0_is_0 R n)) => [| p0N0].
- rewrite coef0_is_0E nth0_trXn coefC /= => /eqP ->.
  by rewrite eq_refl trpolyC0 trpolyC1 exp0.
- rewrite exp_coef0_isnt_0 //.
  move: p0N0; rewrite coef0_is_0E nth0_trXn coefC /= => /negbTE ->.
  by rewrite rmorph0.
Qed.

Lemma log_coef0_is_1 f : f \in coef0_is_1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i).
Proof. by rewrite /log => ->. Qed.

Lemma log_coef0_is_1_val f : f \in coef0_is_1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - val f) ^+i).
Proof.
rewrite /log => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite !linearZ /= !linearN /= val_exp_trpoly trXn_trXn.
Qed.

Lemma log_coef0_isnt_1 f : f \notin coef0_is_1 -> log f = 0.
Proof. by rewrite /log => /negPf ->. Qed.

Lemma log1 : log (1 : {trpoly R n}) = 0.
Proof.
apply/val_inj/polyP=> j; rewrite log_coef0_is_1 ?rpred1 // coef0 coef_trXn.
case: ifP => // j_small; rewrite coefN big1 ?coef0 ?oppr0 //.
by move=> [|i]; rewrite subrr expr0n ?eqxx ?invr0 ?scale0r ?scaler0.
Qed.

End ExpLog.

Arguments log {R n}.
Arguments exp {R n}.

Notation "f ^^ r" := (expr_trpoly r f) : trpoly_scope.


Section DerivComRing.

Variables (R : comRingType) (n : nat).
Implicit Type f : {trpoly R n}.

Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Theorem deriv_trpolyX f m :
  (f ^+ m)^` () = f^`() * (trXn n.-1 f) ^+ m.-1 *+ m.
Proof.
elim: m => /= [|m IHm]; first by rewrite expr0 mulr0n -trpolyC1 deriv_trpolyC.
rewrite exprS deriv_trpolyM {}IHm (mulrC (_ f)) val_exp_trpoly /=.
rewrite mulrC -mulrnAr mulrCA -mulrDr -mulrnAr; congr (_ * _).
rewrite trXnE trXn_trXn ?leq_pred //.
rewrite rmorphX /= mulrnAr -exprS; case: m => /= [|m]; rewrite -?mulrS //.
by rewrite !expr0 mulr0n addr0.
Qed.

End DerivComRing.


Section CoefExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Type f : {trpoly R n}.

Lemma exp_in_coef0_is_1 f : (exp f \in coef0_is_1) = (f \in coef0_is_0).
Proof.
apply/idP/idP => [| Hf].
- apply/contraLR => /exp_coef0_isnt_0 ->.
  by rewrite coef0_is_1E coef0 eq_sym oner_eq0.
- rewrite exp_coef0_is_0 // coef0_is_1_trXn.
  rewrite big_ord_recl /= fact0 invr1 scale1r expr0.
  rewrite addrC coef0_is_1_add01 ?rpred1 //.
  apply rpred_sum => [i _].
  by rewrite coef0_is_0Z // coef0_is_0X.
Qed.

Lemma coef0_exp f : f \in coef0_is_0 -> (exp f)`_0 = 1.
Proof. by rewrite -exp_in_coef0_is_1 coef0_is_1E => /eqP. Qed.

Lemma exp_unit f : f \in coef0_is_0 -> exp f \is a GRing.unit.
Proof. by rewrite -exp_in_coef0_is_1; apply coef0_is_1_unit. Qed.

Lemma log_in_coef0_is_0 f : log f \in coef0_is_0.
Proof.
case (boolP (f \in coef0_is_1)) => [f0_eq1|f0_neq1]; last first.
  by rewrite log_coef0_isnt_1 // rpred0.
rewrite log_coef0_is_1 // coef0_is_0_trXn.
rewrite rpredN big_nat rpred_sum // => [[|i]] // _.
by rewrite coef0_is_0Z // coef0_is_0X // -coef0_is_10.
Qed.

Lemma coef0_log f : (log f)`_0 = 0.
Proof. by have := log_in_coef0_is_0 f; rewrite coef0_is_0E => /eqP. Qed.

End CoefExpLog.


Module TruncPolyUnitRing.

Section PrimitiveUnitRing.

Variable R : unitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

(* Is this useful ? *)
Fact natmul_inj (m : nat) : (m%:R == 0 :> R) = (m == 0%N).
Proof.
case: m => [|m]; first by rewrite eq_refl; apply/eqP.
rewrite {2}/eq_op /=.
apply/negP => /eqP/(congr1 (fun x => x \is a GRing.unit)).
by rewrite nat_unit unitr0.
Qed.

Lemma pred_size_prim (p : {poly R}) : (size (prim p)).-1 = size p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite prim0 size_poly0.
rewrite size_poly_eq // size_poly_eq0 p_neq0 -lead_coefE /=.
have:= p_neq0; rewrite -size_poly_eq0.
case: (size p) => // sz _.
apply/negP => /eqP/(congr1 (fun x => x * sz.+1%:R))/eqP.
by rewrite mul0r divrK // mulr1n lead_coef_eq0 (negbTE p_neq0).
Qed.

Lemma primK : cancel (@prim R) (@deriv R).
Proof.
move=> p.
rewrite /prim -{3}[p]coefK ; apply/polyP => i.
rewrite coef_deriv !coef_poly ltnS.
case: (_ < _); last by rewrite mul0rn.
by rewrite eqn0Ngt ltn0Sn -mulr_natr /= divrK.
Qed.

Implicit Types (f g : {trpoly R n}).

Lemma prim_trpolyK : cancel (@prim_trpoly R n) (@deriv_trpoly R n.+1).
Proof.
move=> p; apply/trpolyP => i le_in.
rewrite coef_deriv_trpoly coef_prim_trpoly.
by rewrite -{2}(primK p) coef_deriv.
Qed.

Lemma deriv_trpolyK :
  {in @coef0_is_0 R n.+1, cancel (@deriv_trpoly R _) (@prim_trpoly R _)}.
Proof.
move=> f; rewrite coef0_is_0E => /eqP f0_eq0.
apply/trpolyP => i _.
rewrite coef_prim_trpoly coef_prim coef_deriv_trpoly.
case: i => [|i]; first by rewrite eq_refl f0_eq0.
by rewrite [_.+1.-1]/= -mulr_natr mulrK.
Qed.

End PrimitiveUnitRing.


Section ExpLogMorph.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.


Lemma nat_unit_alg (A : unitAlgType R) i : i.+1%:R \is a @GRing.unit A.
Proof. by rewrite -scaler_nat scaler_unit ?unitr1 ?nat_unit. Qed.


Implicit Types (f g : {trpoly R n}).

Lemma fact_unit m : m`!%:R \is a @GRing.unit R.
Proof. by have:= fact_gt0 m; rewrite lt0n; case: m`!. Qed.

Theorem expD : {in (@coef0_is_0 R n) &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g f0_eq0 g0_eq0 /=.
rewrite ?(exp_coef0_is_0_val, rpredD) //.
apply/val_inj => /=; apply/val_inj => /=.
rewrite !trXnE trXn_mul.
rewrite !coef0_is_0E -!horner_coef0 in f0_eq0 g0_eq0.
move/eqP: g0_eq0 ; move/eqP : f0_eq0.
case: f g => [f _] [g _] /=.
rewrite !horner_coef0 => f0_eq0 g0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *:
         (\sum_(j < i'.+1) f ^+ (i' - j) * g ^+ j *+ 'C(i', j)))); last first.
  by move => i _ /=; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i'.+1)
        ((j`! * (i' -j)`!)%:R) ^-1 *: (f ^+ (i' - j) * g ^+ j)))); last first.
  move => [i /= _] _.
  rewrite scaler_sumr; apply: eq_bigr => [[j]]; rewrite /= ltnS => le_ji _.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl; congr(_ *: _).
  case: i le_ji => [|i Hi].
    by rewrite leqn0 => /eqP ->; rewrite fact0 bin0 mulr1 muln1.
  rewrite bin_factd //.
  rewrite natr_div ?mulKr ?fact_unit // ?natrM ?unitrM ?fact_unit //.
  by apply/dvdnP; exists 'C(i.+1, j); rewrite bin_fact.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < n.+1)
                    ((i'`! * j`!)%:R^-1) *: (f ^+ i' * g ^+ j)))); last first.
  move => i _.
  rewrite (big_distrr _ _ _) /=.
  apply: eq_bigr => j _ /=.
  rewrite -scalerAl -scalerCA -scalerAl scalerA -invrM ?unitfE ?fact_unit //.
 by rewrite -natrM mulnC.
rewrite !trXnE.
have -> : trXn n (\sum_(i < n.+1) \sum_(j < n.+1)
                   (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j))  =
          trXn n (\sum_(i < n.+1) \sum_(j < n.+1 | i + j <= n)
                   (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)).
  rewrite !rmorph_sum; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !rmorph_sum.
  rewrite (bigID (fun j => i + (nat_of_ord j) <= n)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= n))
                      (fun j => trXn n ((i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)))).
  apply: big1_seq => /= j.
  rewrite -ltnNge; move/andP => [ n_lt_addij _]; rewrite linearZ /=.
  by rewrite trXnMX_eq0 // scaler0.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < n.+1 |
        i' + j < n.+1) (i'`! * j`!)%:R^-1 *: (f ^+ i' * g ^+ j))); last first.
  move => i _ /=.
  by apply: eq_bigr.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < i'.+1)
           (j`! * (i' - j)`!)%:R^-1 *: (f ^+ j * g ^+ (i' - j)))); last first.
  move => i _ /=.
  rewrite -(big_mkord predT (fun j => (j`! * (i - j)`!)%:R^-1 *:
                                                       (f ^+ (i - j) * g ^+ j))).
  rewrite big_nat_rev big_mkord add0n.
  apply: eq_bigr => j _.
  by rewrite !subSS subnBA -1?ltnS // !addKn mulnC.
by rewrite (triangular_index_bigop _
                      (fun i j => (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j))) /=;
  last exact: ltnSn.
Qed.

Lemma expN f : f \in coef0_is_0 -> exp (- f) = (exp f)^-1.
Proof.
move=> f0_eq0; apply: (@mulrI _ (exp f)); rewrite ?divrr ?exp_unit //.
by rewrite -expD ?rpredN // subrr exp0.
Qed.

Lemma expB : {in (@coef0_is_0 R n) &, {morph exp : f g / f - g >-> f / g}}.
Proof. by move=> f g hf hg; rewrite expD ?rpredN // expN. Qed.


Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Lemma deriv_trpoly_eq0_cst f : f^`() = 0 -> {c : R | f = c %:S}.
Proof.
move: f; case: n => [f _| m f]; first by rewrite [f]trpoly_is_cst; exists (f`_0).
move=> H; exists (f`_0).
apply/trpolyP => [] [|i]; rewrite coef_trpolyC // ltnS [RHS]/= => le_im.
apply: (mulIr (nat_unit i)); rewrite mul0r.
move: H => /(congr1 (fun x : {trpoly _ _ } => x`_i)).
by rewrite coef_deriv_trpoly coef0 -mulr_natr.
Qed.

Lemma deriv_trpoly_eq0 f :
  f^`() = 0 -> {x : R | (val f).[x] = 0} -> f = 0.
Proof.
move=> /deriv_trpoly_eq0_cst [c ->] [x].
rewrite val_trpolyC /= hornerC => ->.
by rewrite trpolyC0.
Qed.

Lemma deriv_trpoly_eq f g :
  f ^` () = g ^` () -> {x : R | (val f).[x] = (val g).[x]} -> f = g.
Proof.
move=> H [x Hx].
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_trpoly_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

End ExpLogMorph.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {trpoly R n}).

Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Theorem deriv_exp f : (exp f)^` () = f^` () * (trXn n.-1 (exp f)).
Proof.
move: f; case: n => /= [| m] f.
  by rewrite [f]trpoly_is_cst deriv_trpolyC mul0r expC deriv_trpolyC.
case: (boolP (f \in coef0_is_0)) => [p0_eq0 | p0_neq0]; last first.
  by rewrite exp_coef0_isnt_0 // deriv_trpoly0 rmorph0 mulr0.
rewrite !exp_coef0_is_0_val //= !deriv_trpolyE //=; apply/val_inj => /=.
rewrite deriv_trXn !trXnE trXn_trXn // trXn_trXn //.
rewrite deriv_sum -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= !trXnE rmorphD linearZ /=.
rewrite !trXnE trXn_eq0 //; last by apply/eqP; rewrite -coef0_is_0E.
rewrite scaler0 addr0 trXn_mul mulr_sumr.
rewrite -(big_mkord predT (fun i => deriv (i`!%:R^-1 *: (val f) ^+ i))) /=.
rewrite big_nat_recl // expr0 linearZ /= derivC scaler0 add0r.
rewrite !trXnE; congr (val (trXn _ _)); apply: eq_bigr => i _.
rewrite linearZ /= deriv_exp /= -scalerCA -scaler_nat.
rewrite scalerA -scalerAl; congr (_ *: _).
rewrite factS natrM /= invrM ?fact_unit //.
rewrite -mulrA [X in _ * X]mulrC.
by rewrite divrr // mulr1.
Qed.

Theorem deriv_log f :
  f \in coef0_is_1 -> (log f) ^` () = (f )^` () / (trXn n.-1 f).
Proof.
case: n f => [|m] f.
  rewrite [f]trpoly_is_cst coef0_is_1E nth0_trXn coefC eqxx => /eqP ->.
  by rewrite !deriv_trpoly0p mul0r.
move => f0_is_1.
rewrite log_coef0_is_1_val // rmorphN rmorph_sum linearN raddf_sum -sumrN.
rewrite big_nat.
rewrite (eq_bigr (fun i => (f )^` () * ((1 - (trXn m f)) ^+ i.-1))) =>
                                                  [|i /andP [hi _]]; last first.
- rewrite linearZ rmorphX /= deriv_trpolyZ rmorphB rmorph1 /= deriv_trpolyX.
  rewrite linearB rmorphB rmorph1 -trpolyC1 /= deriv_trpolyC sub0r /= trXn_trXn //.
  rewrite -scaler_nat scalerA mulrC divrr; last by case: i hi.
  by rewrite scale1r mulNr opprK trpolyK.
- rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : trXn m f \is a GRing.unit.
    by rewrite trXn_unitE -unit_trpolyE coef0_is_1_unit.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  rewrite expr_coef0_is_0 ?subr0 //.
  by rewrite -coef0_is_10 coef0_is_1_trXn.
Qed.

Lemma expK : {in coef0_is_0, cancel (@exp R n) (@log R n)}.
Proof.
move => f f0_eq0 /=.
apply/eqP; rewrite -(subr_eq0 _ f); apply/eqP.
apply: (deriv_trpoly_eq0 nat_unit).
- rewrite linearB /= deriv_log ?exp_in_coef0_is_1 //.
  rewrite deriv_exp // -mulrA divrr ?mulr1 ?subrr // trXn_unitE.
  by rewrite coef0_exp // unitr1.
- exists 0; rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0.
  by rewrite coef0_log sub0r; apply/eqP; rewrite oppr_eq0 -coef0_is_0E.
Qed.

Lemma exp_inj : {in coef0_is_0 &, injective (@exp R n)}.
Proof. exact: (can_in_inj expK). Qed.

Lemma log_inj : {in coef0_is_1 &, injective (@log R n)}.
Proof.
move=> p q p0_eq0 q0_eq0 /= Hlog.
have {Hlog} : (p/q) ^` () = 0.
  rewrite deriv_div_trpoly; last exact: coef0_is_1_unit.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  apply/eqP; rewrite subr_eq0 [trXn n.-1 p * q^`()%trpoly]mulrC.
  rewrite -eq_divr ?trXn_unitE -?unit_trpolyE ?coef0_is_1_unit //.
  by move/(congr1 (@deriv_trpoly R n)): Hlog; rewrite !deriv_log // => ->.
move/(deriv_trpoly_eq0_cst nat_unit) => [c Hpq].
suff Hc : c = 1 by subst c; move: Hpq; rewrite trpolyC1; apply: divr1_eq.
move/(congr1 (fun x => x * q)): Hpq.
rewrite mulrAC -mulrA divrr ?trXn_unitE -?unit_trpolyE ?coef0_is_1_unit //.
rewrite mulr1 -alg_trpolyC mulr_algl=> /(congr1 (fun x : {trpoly R n} => x`_0)).
rewrite coefZ.
move: p0_eq0 q0_eq0; rewrite !coef0_is_1E => /eqP -> /eqP ->.
by rewrite mulr1 => ->.
Qed.

Lemma logK : {in coef0_is_1 , cancel (@log R n) (@exp R n)}.
Proof.
move=> p p0_eq1 /=.
apply: log_inj => //; first by rewrite exp_in_coef0_is_1 log_in_coef0_is_0.
by rewrite expK // log_in_coef0_is_0.
Qed.

Lemma logM : {in (@coef0_is_1 R n) &, {morph log : f g / f * g >-> f + g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
apply exp_inj; rewrite ?rpredD ?log_in_coef0_is_0 //.
rewrite expD ?log_in_coef0_is_0 //.
by rewrite !logK // rpredM.
Qed.


Section ExprTrpoly.

Variable f : {trpoly R n}.
Hypothesis f0_eq1 : f \in coef0_is_1.

Let log_coef0_is_0Z c : c *: log f \in coef0_is_0.
Proof. by rewrite coef0_is_0Z // log_in_coef0_is_0. Qed.

Lemma coef0_is_1_expr c : f ^^ c \in coef0_is_1.
Proof. by rewrite /expr_trpoly exp_in_coef0_is_1 log_coef0_is_0Z. Qed.

Lemma exp_logX m : f ^+ m = exp (log f *+ m).
Proof.
elim: m => [|m IHm]; first by rewrite expr0 mulr0n exp0.
rewrite exprS mulrS expD ?rpredMn ?log_in_coef0_is_0 //.
by rewrite -IHm logK.
Qed.

Lemma expr_trpolyn m : f ^^ m%:R = f ^+ m.
Proof. by rewrite /expr_trpoly exp_logX // scaler_nat. Qed.

Lemma expr_trpoly1 : f ^^ 1 = f.
Proof. by rewrite -[1]/(1%:R) expr_trpolyn expr1. Qed.

Lemma expr_trpoly0 : f ^^ 0 = 1.
Proof. by rewrite -[0]/(0%:R) expr_trpolyn expr0. Qed.

Lemma expr_trpolyN a : f ^^ (- a) = (f ^^ a)^-1.
Proof. by rewrite /expr_trpoly scaleNr expN. Qed.

Lemma expr_trpolyN1 : f ^^ (-1) = f ^-1.
Proof. by rewrite expr_trpolyN expr_trpoly1. Qed.

Lemma expr_trpolyD a b : f ^^ (a + b) = (f ^^ a) * (f ^^ b).
Proof. by rewrite /expr_trpoly scalerDl expD. Qed.

Lemma expr_trpolyB a b : f ^^ (a - b) = (f ^^ a) / (f ^^ b).
Proof. by rewrite expr_trpolyD expr_trpolyN. Qed.

Lemma expr_trpolyM a b : f ^^ (a * b) = (f ^^ a) ^^ b.
Proof. by rewrite /expr_trpoly expK ?scalerA ?[b * a]mulrC. Qed.

Lemma deriv_expr_trpoly a :
  (f ^^ a) ^`() = a *: trXn n.-1 (f ^^ (a - 1)) * f^`().
Proof.
rewrite {1}/expr_trpoly deriv_exp -/(f ^^ a).
rewrite linearZ /= deriv_log // -!scalerAl; congr (_ *: _).
rewrite -mulrA mulrC; congr (_ * _).
rewrite -trXnV ?leq_pred // -rmorphM /=.
rewrite mulrC expr_trpolyB expr_trpoly1.
by rewrite /= trXnE trXn_trXn // leq_pred.
Qed.

End ExprTrpoly.

Lemma expr_trpolyK a : a \is a GRing.unit ->
  {in coef0_is_1, cancel (@expr_trpoly R n a) (@expr_trpoly R n a^-1)}.
Proof. by move=> aU f f0_eq1; rewrite -expr_trpolyM divrr ?expr_trpoly1. Qed.

Lemma expr_trpoly_inj a : a \is a GRing.unit ->
  {in coef0_is_1 &, injective (@expr_trpoly R n a)}.
Proof. by move=> /expr_trpolyK/can_in_inj. Qed.


Local Notation "\sqrt f" := (f ^^ (2%:R^-1)).

Lemma sqrrK f :
  f \in coef0_is_1 -> \sqrt (f ^+ 2) = f :> {trpoly R n}.
Proof.
by move => Hh; rewrite -expr_trpolyn -?expr_trpolyM ?divrr ?expr_trpoly1.
Qed.

Lemma sqrtK f :
  f \in coef0_is_1 -> (\sqrt f) ^+ 2 = f :> {trpoly R n}.
Proof.
move => Hh; rewrite -expr_trpolyn ?coef0_is_1_expr //.
by rewrite -?expr_trpolyM // mulrC divrr ?expr_trpoly1.
Qed.

End DerivExpLog.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : trpoly_scope.


Section CoefExpX.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma coef1cX p c : 1 + c *: \Xo(p) \in @coef0_is_1 R p.
Proof.
by rewrite coef0_is_1E coefD coef1 coefZ coef_trXn coefX mulr0 addr0.
Qed.

Lemma deriv1cX p c : (1 + c *: \Xo(p.+1)) ^` () = c%:S :> {trpoly R p}.
Proof.
rewrite linearD /= deriv_trpoly1 add0r linearZ /=.
rewrite -alg_trpolyC; congr (_ *: _); apply val_inj.
by rewrite (val_deriv_trpoly \Xo(p.+1)) val_trpolyX scale1r derivX.
Qed.

Theorem coef_expr1cX c a m p : m <= p ->
  ((1 + c *: \Xo(p)) ^^ a)`_m = c ^+ m * \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
elim: m p a => [|m IHm] p a lt_mp.
  rewrite big_ord0 /expr_trpoly coef0_exp ?coef0_is_0Z ?log_in_coef0_is_0 //.
  by rewrite expr0 mul1r fact0 divr1.
case: p lt_mp => [|p] //; rewrite ltnS => le_mp.
have:= coef_deriv_trpoly ((1 + c *: \Xo(p.+1)) ^^ a) m.
rewrite -mulr_natr => /(congr1 (fun x => x * m.+1%:R^-1)).
rewrite mulrK // => <-.
rewrite deriv_expr_trpoly ?coef1cX // deriv1cX.
rewrite [_ * c%:S]mulrC -alg_trpolyC mulr_algl exprS coefZ.
rewrite coefZ coef_trXn le_mp {}IHm ?(leq_trans le_mp) // {p le_mp}.
rewrite mulrA factS natrM invrM // ?fact_unit // !mulrA; congr (_ * _ * _).
rewrite -[_ * a * _]mulrA [a * _]mulrC -!mulrA; congr (_ * (_ * _)).
rewrite big_ord_recl /= subr0; congr (_ * _).
by apply eq_bigr => i /= _; rewrite /bump /= natrD -[1%:R]/1 opprD addrA.
Qed.

Lemma coef_expr1X a m p :
  m <= p -> ((1 + \Xo(p)) ^^ a)`_m = \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
by move=> le_mp; rewrite -[\X]scale1r coef_expr1cX // expr1n mul1r.
Qed.

End CoefExpX.


Section SquareRoot.

Variables R : idomainType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {trpoly R n}).


Lemma sqrtE f g : f \in coef0_is_1 -> g ^+ 2 = f ->
  g = \sqrt f  \/  g = - \sqrt f.
Proof.
move=> /eqP f0_eq1 Heq.
have /eqP := (congr1 (fun f : {trpoly R n} => f`_0) Heq).
rewrite -subr_eq0 {}f0_eq1 expr2 coef0_trpolyM -expr2 subr_sqr_1.
rewrite mulf_eq0 => /orP [].
- by rewrite subr_eq0 -coef0_is_1E -{}Heq {f} => Hg0; left; rewrite sqrrK.
- rewrite addr_eq0 -eqr_oppLR -coefN -raddfN -coef0_is_1E -{}Heq {f} => Hg0.
  by right; apply oppr_inj; rewrite opprK -sqrrN sqrrK.
Qed.

End SquareRoot.

End TruncPolyUnitRing.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : trpoly_scope.


Module TruncPolyField.

Section TruncPolyField.

Variables K : fieldType.
Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma nat_unit_field i : i.+1%:R \is a @GRing.unit K.
Proof. by rewrite unitfE; move: char_K_is_zero => /charf0P ->. Qed.

Local Notation nuf := nat_unit_field.

Definition nat_unit_alg         := TruncPolyUnitRing.nat_unit_alg         nuf.
Definition pred_size_prim       := TruncPolyUnitRing.pred_size_prim       nuf.
Definition primK                := TruncPolyUnitRing.primK                nuf.
Definition prim_trpolyK         := TruncPolyUnitRing.prim_trpolyK         nuf.
Definition deriv_trpolyK        := TruncPolyUnitRing.deriv_trpolyK        nuf.
Definition expD                 := TruncPolyUnitRing.expD                 nuf.
Definition expN                 := TruncPolyUnitRing.expN                 nuf.
Definition expB                 := TruncPolyUnitRing.expB                 nuf.
Definition deriv_trpoly_eq0_cst := TruncPolyUnitRing.deriv_trpoly_eq0_cst nuf.
Definition deriv_trpoly_eq0     := TruncPolyUnitRing.deriv_trpoly_eq0     nuf.
Definition deriv_trpoly_eq      := TruncPolyUnitRing.deriv_trpoly_eq      nuf.
Definition deriv_exp            := TruncPolyUnitRing.deriv_exp            nuf.
Definition deriv_log            := TruncPolyUnitRing.deriv_log            nuf.
Definition expK                 := TruncPolyUnitRing.expK                 nuf.
Definition log_inj              := TruncPolyUnitRing.log_inj              nuf.
Definition logK                 := TruncPolyUnitRing.logK                 nuf.
Definition logM                 := TruncPolyUnitRing.logM                 nuf.
Definition exp_logX             := TruncPolyUnitRing.exp_logX             nuf.
Definition expr_trpolyn         := TruncPolyUnitRing.expr_trpolyn         nuf.
Definition expr_trpoly0         := TruncPolyUnitRing.expr_trpoly0         nuf.
Definition expr_trpoly1         := TruncPolyUnitRing.expr_trpoly1         nuf.
Definition expr_trpolyN         := TruncPolyUnitRing.expr_trpolyN         nuf.
Definition expr_trpolyD         := TruncPolyUnitRing.expr_trpolyD         nuf.
Definition expr_trpolyB         := TruncPolyUnitRing.expr_trpolyB         nuf.
Definition expr_trpolyM         := TruncPolyUnitRing.expr_trpolyM         nuf.

End TruncPolyField.

End TruncPolyField.

Import TruncPolyField.
