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


Lemma expr_prod i (R : ringType) (x : R) : x ^+ i = \prod_(j < i) x.
Proof.
elim: i => [|i IHi]; first by rewrite expr0 big_ord0.
by rewrite big_ord_recl -IHi exprS.
Qed.


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


Section MorePolyTheory.

Variable R : ringType.
Implicit Type p q : {poly R}.

Lemma poly_cat p n :
  Poly (take n p) + 'X^n * Poly (drop n p) = p.
Proof.
apply/polyP=> i; rewrite coefD coefXnM !coef_Poly; case: ltnP => Hi.
by rewrite nth_take // addr0.
rewrite nth_drop subnKC // [(take _ _)`_i]nth_default ?add0r //.
by rewrite size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

Fact coef0M p q : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed.

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

Fact coef0_eq_coef0 (p q : {poly K}) :
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

Fact size_deriv (p : {poly K}) : size (p^`()%R) = (size p).-1.
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

Lemma deriv_eq0 (p : {poly K}) : p^`() = 0 -> {c : K | p = c %:P}.
Proof.
move/eqP ; rewrite -size_poly_eq0 size_deriv.
move/eqP => H_size_p.
exists p`_0 ; apply: size1_polyC.
by rewrite (leq_trans (leqSpred _)) // H_size_p.
Qed.

End MorePolyTheory.


Section TruncPolyDef.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}).

Record trunc_polynomial :=
  TruncPolynomial { trpoly : {poly R}; _ : size trpoly <= n.+1 }.

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

Fact truncpoly_key : unit. Proof. by []. Qed.
Definition truncpoly : trpoly_of (Phant R) -> {poly R} :=
  locked_with truncpoly_key trpoly.
Canonical truncpoly_unlockable := [unlockable fun truncpoly].

Lemma trpolyE : trpoly =1 truncpoly.
Proof. by case=> p Hp; rewrite unlock. Qed.

Coercion seq_of_trpoly (f : trunc_polynomial) : seq R := @trpoly f.

Lemma size_trpoly (f : trpoly_of (Phant R)) : size f <= n.+1.
Proof. by case: f. Qed.

Definition coeftrp_head h i (p : trpoly_of (Phant R)) := let: tt := h in p`_i.

End TruncPolyDef.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope ring_scope with trpoly_of.
Bind Scope ring_scope with trunc_polynomial.
Arguments trpoly {R n%N}.
Arguments trpoly_inj {R} [p1%R p2%R] : rename.
Notation "{ 'trpoly' R n }" :=  (trpoly_of n (Phant R)).
Arguments coeftrp_head {R n} h i%N p%R.
Notation coeftrp i := (coeftrp_head tt i).

Hint Resolve size_trpoly.


Section CoefTruncPoly.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}) (f g : {trpoly R n}).

Lemma coef_trpolyE f i : f`_i = (trpoly f)`_i.
Proof. by []. Qed.

Lemma coef_trpoly f i : f`_i = if i <= n then f`_i else 0.
Proof.
case: (leqP i n) => Hi //.
by rewrite nth_default // (leq_trans (size_trpoly _) Hi).
Qed.

Lemma trpolyP f g : (forall i, i <= n -> f`_i = g`_i) <-> (f = g).
Proof.
split => [H | H i Hi].
- apply/trpoly_inj/polyP => i; rewrite [LHS]coef_trpoly [RHS]coef_trpoly.
  by case: leqP => //; apply: H.
- move: H => /(congr1 trpoly)/(congr1 (fun r => r`_i)).
  by rewrite coef_trpoly Hi.
Qed.


Definition Trpoly_of (p : {poly R}) (p_small : size p <= n.+1)
  : {trpoly R n} := TruncPolynomial p_small.

Fact trXn_subproof p : size (Poly (take n.+1 p)) <= n.+1.
Proof. by apply: (leq_trans (size_Poly _)); rewrite size_take geq_minl. Qed.
Definition trXn_def p := Trpoly_of (trXn_subproof p).
Fact trXn_key : unit. Proof. by []. Qed.
Definition trXn := locked_with trXn_key trXn_def.
Canonical trXn_unlockable := [unlockable fun trXn].

Definition trpolyC_def c := trXn (c %:P).
Fact trpolyC_key : unit. Proof. by []. Qed.
Definition trpolyC := locked_with trpolyC_key trpolyC_def.
Canonical trpolyC_unlockable := [unlockable fun trpolyC].

Definition trpoly_of_fun (f : nat -> R) := Trpoly_of (size_poly _ f).

Lemma trXnE p : trpoly (trXn p) = Poly (take n.+1 p) :> {poly R}.
Proof. by rewrite unlock. Qed.

Lemma coef_trXn p i : (trXn p)`_i = if i <= n then p`_i else 0.
Proof.
rewrite coef_trpolyE trXnE coef_Poly.
case: leqP => Hi; first by rewrite nth_take.
by rewrite nth_default // size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

Lemma trXnP p q : (forall i, i <= n -> p`_i = q`_i) <-> (trXn p = trXn q).
Proof.
rewrite -trpolyP; split => H i Hi.
- by rewrite !coef_trXn Hi; apply H.
- by have := H i Hi; rewrite !coef_trXn Hi.
Qed.

Lemma trpolyK : cancel (@trpoly R n) trXn.
Proof. by move=> f; apply/trpolyP => i Hi; rewrite coef_trXn Hi. Qed.

Lemma coef0_trXn (p : {poly R}) : (trXn p)`_0 = p`_0.
Proof. by rewrite coef_trXn leq0n. Qed.


Lemma trpolyCE c : trpolyC c = trXn c%:P.
Proof. by rewrite unlock. Qed.

Lemma coef_trpolyC c i : (trpolyC c)`_i = if i == 0%N then c else 0.
Proof.
by rewrite trpolyCE coef_trXn coefC; case: i => //= i; rewrite if_same.
Qed.

Lemma val_trpolyC (c : R) : trpoly (trpolyC c) = c %:P.
Proof. by apply/polyP => i /=; rewrite coef_trpolyC coefC. Qed.

Lemma trpolyCK : cancel trpolyC (coeftrp 0).
Proof. by move=> c; rewrite [coeftrp 0 _]coef_trpolyC. Qed.


Lemma trpolyC_inj : injective trpolyC.
Proof.
by move=> c1 c2 eqc12; have:= coef_trpolyC c2 0; rewrite -eqc12 coef_trpolyC.
Qed.


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
Notation "c %:S" := (trpolyC _ c) (at level 2) : trpoly_scope.
Notation "\X" := (trXn _ 'X) : trpoly_scope.
Notation "\Xo( n )" := (trXn n 'X) (only parsing): trpoly_scope.


Section TruncPolyTheory.

Variable (R : ringType).
Implicit Types (p q r s : {poly R}).

Fact trXnC n a : trpoly (trXn n a%:P) = a%:P :> {poly R}.
Proof.
apply/polyP => i; rewrite coef_trXn coefC.
by case: eqP => [->|_] //; rewrite if_same.
Qed.

Fact trXn_trXn p m n : m <= n -> trXn m (trpoly (trXn n p)) = trXn m p.
Proof.
move=> le_mn; apply/trXnP => i le_im.
by rewrite coef_trXn (leq_trans le_im le_mn).
Qed.

Variable (n : nat).

Lemma trXnCE m a : trXn n (trpoly (a%:S : {trpoly R m})) = a%:S.
Proof. by apply trpoly_inj; rewrite val_trpolyC !trpolyCE. Qed.

Lemma trXn_mull p q : trXn n (trpoly (trXn n p) * q) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans le_ji le_in).
Qed.

Lemma trXn_mulr p q : trXn n (p * trpoly (trXn n q)) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans (leq_subr _ _) le_in).
Qed.

Lemma trXn_mul p q :
  trXn n (trpoly (trXn n p) * trpoly (trXn n q)) = trXn n (p * q).
Proof. by rewrite trXn_mulr trXn_mull. Qed.


(* zmodType structure *)
Implicit Types (f g : {trpoly R n}).

Fact zero_trpoly_subproof : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.
Definition zero_trpoly := Trpoly_of zero_trpoly_subproof.

Lemma add_trpoly_subproof f g :
  size (trpoly f + trpoly g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_trpoly. Qed.
Definition add_trpoly f g := Trpoly_of (add_trpoly_subproof f g).

Lemma opp_trpoly_subproof f : size (- trpoly f) <= n.+1.
Proof. by rewrite size_opp ?size_trpoly. Qed.
Definition opp_trpoly f := Trpoly_of (opp_trpoly_subproof f).

Program Definition trpoly_zmodMixin :=
  @ZmodMixin {trpoly R n} zero_trpoly opp_trpoly add_trpoly _ _ _ _.
Next Obligation. by move => f1 f2 f3; apply/trpoly_inj/addrA. Qed.
Next Obligation. by move => f1 f2; apply/trpoly_inj/addrC. Qed.
Next Obligation. by move => f; apply/trpoly_inj/add0r. Qed.
Next Obligation. by move => f; apply/trpoly_inj/addNr. Qed.
Canonical trpoly_zmodType := ZmodType {trpoly R n} trpoly_zmodMixin.

Fact trXn_is_additive : additive (trXn n).
Proof.
by move=> f g; apply/trpolyP => i Hi; rewrite coefB !coef_trXn coefB Hi.
Qed.
Canonical trXn_additive := Additive trXn_is_additive.

Lemma trXn0 : trXn n 0 = 0.
Proof. exact: raddf0. Qed.

Fact trpoly_is_additive : additive (@trpoly R n : {trpoly R n} -> {poly R}).
Proof. by []. Qed.
Canonical trpoly_additive := Additive trpoly_is_additive.

Lemma trpolyC_is_additive : additive (@trpolyC R n : R -> {trpoly R n}).
Proof.
move=> c1 c2; apply trpoly_inj.
by rewrite !val_trpolyC !raddfB /= !val_trpolyC.
Qed.
Canonical trpolyC_additive := Additive trpolyC_is_additive.

Lemma trpolyC0 : (0%:S : {trpoly R n}) = 0.
Proof. exact: raddf0. Qed.


(* ringType structure *)
Fact one_trpoly_proof : size (1 : {poly R}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.
Definition one_trpoly : {trpoly R n} := Trpoly_of one_trpoly_proof.

Definition mul_trpoly f g := trXn n (trpoly f * trpoly g).
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
Next Obligation. move=> f1 f2 f3;
                 by rewrite /mul_trpoly trXn_mulr trXn_mull mulrA. Qed.
Next Obligation. by move=> p; rewrite /mul_trpoly mul1r trpolyK. Qed.
Next Obligation. by move=> p; rewrite /mul_trpoly mulr1 trpolyK. Qed.
Next Obligation. by move=> f1 f2 f3; rewrite /mul_trpoly mulrDl raddfD. Qed.
Next Obligation. by move=> f1 f2 f3; rewrite /mul_trpoly mulrDr raddfD. Qed.
Next Obligation. by rewrite -val_eqE oner_neq0. Qed.
Canonical trpoly_ringType := RingType {trpoly R n} trpoly_ringMixin.


Lemma trXn1 : trXn n 1 = 1.
Proof. by apply/trpolyP => i Hi; rewrite coef_trXn Hi. Qed.

Fact trXn_is_multiplicative : multiplicative (@trXn R n).
Proof. by split => [f g|] /=; [rewrite -trXn_mul | rewrite trXn1]. Qed.
Canonical trXn_multiplicative := AddRMorphism trXn_is_multiplicative.

Lemma mul_trpoly_val f g : f * g = trXn n (trpoly f * trpoly g).
Proof. by []. Qed.

Lemma coefM_trpoly f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_j * g`_(i - j) else 0.
Proof. by rewrite !coef_trpolyE mul_trpoly_val coef_trXn coefM. Qed.

Lemma coefMr_trpoly f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_(i - j) * g`_j else 0.
Proof. by rewrite !coef_trpolyE mul_trpoly_val coef_trXn coefMr. Qed.

Lemma exp_trpoly_val f (m : nat) : f ^+ m = trXn n ((trpoly f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphX /= trpolyK -exprS.
Qed.

Lemma trpolyC_is_multiplicative :
  multiplicative (@trpolyC R n : R -> {trpoly R n}).
Proof.
split => [c1 c2|]; last by rewrite trpolyCE trXn1.
apply trpoly_inj; rewrite mul_trpoly_val !val_trpolyC -rmorphM /=.
apply/polyP => i; rewrite coef_trpoly coef_trXn coefC; case: i => //= i.
by rewrite !if_same.
Qed.
Canonical trpolyC_rmorphism := AddRMorphism trpolyC_is_multiplicative.

Lemma trpolyC1 : (1%:S : {trpoly R n}) = 1.
Proof. exact: rmorph1. Qed.

Lemma trpolyCM :
  {morph (fun x => (x%:S : {trpoly R n})) : a b / a * b >-> a * b}.
Proof. exact: rmorphM. Qed.


(* lmodType structure *)
Lemma scale_trpoly_subproof (c : R) f : size (c *: val f) <= n.+1.
Proof. exact: leq_trans (size_scale_leq _ _) (size_trpoly _). Qed.
Definition scale_trpoly (c : R) f := Trpoly_of (scale_trpoly_subproof c f).

Program Definition trpoly_lmodMixin :=
  @LmodMixin R [zmodType of {trpoly R n}] scale_trpoly _ _ _ _.
Next Obligation. by apply/trpolyP => i le_in /=; rewrite !coefZ mulrA. Qed.
Next Obligation.
  by move=> x; apply/trpolyP => i le_in; rewrite coef_trpolyE /= scale1r. Qed.
Next Obligation.
  by move=> r x y; apply/trpolyP => i; rewrite coef_trpolyE /= scalerDr. Qed.
Next Obligation.
  by move=> r s; apply/trpolyP => i; rewrite coef_trpolyE /= scalerDl. Qed.
Canonical trpoly_lmodType :=
  Eval hnf in LmodType R {trpoly R n} trpoly_lmodMixin.

Fact trXn_is_linear : linear (@trXn R n).
Proof.
move=> c f g; apply/trpolyP => i Hi.
by rewrite !(coefD, coefZ, coef_trXn) Hi.
Qed.
Canonical trXn_linear := AddLinear trXn_is_linear.

Fact trpoly_is_linear : linear (@trpoly R n : {trpoly R n} -> {poly R}).
Proof. by []. Qed.
Canonical trpoly_linear := AddLinear trpoly_is_linear.


(* lalgType structure *)
Fact scale_trpolyAl c f g : scale_trpoly c (f * g) = (scale_trpoly c f) * g.
Proof.
by apply trpoly_inj; rewrite /= -linearZ  /= !mul_trpoly_val -scalerAl linearZ.
Qed.
Canonical trpoly_lalgType :=
  Eval hnf in LalgType R {trpoly R n} scale_trpolyAl.
Canonical trXn_lrmorphism := AddLRMorphism trXn_is_linear.


Lemma alg_trpolyC (c : R) : c%:A = c%:S.
Proof. by apply/trpoly_inj; rewrite {1}val_trpolyC -alg_polyC. Qed.

(* Test *)
Example trpoly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Example trpoly1 : trXn n (1 : {poly R}) = 1.
Proof. by rewrite rmorph1. Qed.

Lemma trXnZ (c : R) (p : {poly R}) : trXn n (c *: p) =  c *: (trXn n p).
Proof. by rewrite linearZ. Qed.


Local Notation "f *h g" := (hmul_trpoly f g) (at level 2).

Lemma hmul_trpolyr1 f : f *h 1 = (f`_0)%:S.
Proof.
apply/trpolyP => i.
rewrite coef_trpolyC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_trpoly1r f : 1 *h f = (f`_0)%:S.
Proof.
apply/trpolyP => i.
rewrite coef_trpolyC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mul1r ?mul0r.
Qed.

Lemma trpoly_is_cst (g : {trpoly R 0}) : g = (g`_0) %:S.
Proof.
apply/trpoly_inj; rewrite val_trpolyC.
by apply: size1_polyC; rewrite size_trpoly.
Qed.


Lemma coeftrpE f i : coeftrp i f = coefp i (trpoly f).
Proof. by rewrite /= coef_trpolyE. Qed.

Fact coeftrp_is_additive i :
  additive (coeftrp i : {trpoly R n} -> R).
Proof. by move=> f g; exact: coefB. Qed.
Canonical coeftrp_additive i := Additive (coeftrp_is_additive i).
Lemma coeftrD f g i : (f + g)`_i = f`_i + g`_i.
Proof. exact: (raddfD (coeftrp_additive i)). Qed.
Lemma coeftrN f i : (- f)`_i = - f`_i.
Proof. exact: (raddfN (coeftrp_additive i)). Qed.
Lemma coeftrB f g i : (f - g)`_i = f`_i - g`_i.
Proof. exact: (raddfB (coeftrp_additive i)). Qed.
Lemma coeftrMn f k i : (f *+ k)`_i = f`_i *+ k.
Proof. exact: (raddfMn (coeftrp_additive i)). Qed.
Lemma coeftrMNn f k i : (f *- k)`_i = f`_i *- k.
Proof. exact: (raddfMNn (coeftrp_additive i)). Qed.
Lemma coeftr_sum I (r : seq I) (P : pred I) (F : I -> {trpoly R n}) k :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. exact: (raddf_sum (coeftrp_additive k)). Qed.

Fact coeftrp_is_linear i :
  scalable_for *%R (coeftrp i : {trpoly R n} -> R).
Proof. by move=> c g; rewrite /= !coef_trpolyE !linearZ coefZ. Qed.
Canonical coeftrp_linear i := AddLinear (coeftrp_is_linear i).

Lemma coeftrZ a f i : (a *: f)`_i = a * f`_i.
Proof. exact: (scalarZ [linear of (coeftrp i)]). Qed.


Fact coeftrp0_is_multiplicative :
  multiplicative (coeftrp 0 : {trpoly R n} -> R).
Proof.
split=> [p q|]; rewrite !coeftrpE; last by rewrite polyCK.
rewrite mul_trpoly_val /= -!/(_`_0) coef_trXn /= -!/(_`_0) -!/(coefp 0 _).
by rewrite rmorphM.
Qed.
Canonical coeftrp0_rmorphism := AddRMorphism coeftrp0_is_multiplicative.
Canonical coeftrp0_lrmorphism := [lrmorphism of coeftrp 0].

Fact coef0_trpolyM f g : (f * g)`_0 = f`_0 * g`_0.
Proof. exact: (rmorphM coeftrp0_rmorphism). Qed.
Fact coef0_trpolyX f i : (f ^+ i)`_0 = f`_0 ^+ i.
Proof. exact: (rmorphX coeftrp0_rmorphism). Qed.

End TruncPolyTheory.


Section TrXns.

Variable R : ringType.

Definition trXns m n : {trpoly R m} -> {trpoly R n} :=
  @trXn R n \o (@trpoly R m).

Variables (m n p : nat).
Implicit Type (f : {trpoly R m}).

Lemma trXnsE f : trXns n f = trXn n (trpoly f).
Proof. by []. Qed.

Lemma trXns_id f : trXns m f = f.
Proof. by rewrite /trXns /= trpolyK. Qed.

Fact trXns_trXns f :
  p <= n -> trXns p (trXns n f) = trXns p f.
Proof. exact: trXn_trXn. Qed.

Lemma trXnsC a : trXns n (a%:S : {trpoly R m}) = a%:S.
Proof. exact: trXnCE. Qed.

Lemma trXns0 : @trXns m n 0 = 0.
Proof. exact: trXn0. Qed.
Lemma trXns1 : @trXns m n 1 = 1.
Proof. exact: trXn1. Qed.

Fact trXns_is_additive : additive (@trXns m n).
Proof. by move=> f g; rewrite !trXnsE !raddfB. Qed.
Canonical trXns_additive := Additive trXns_is_additive.
Fact trXns_is_linear : linear (@trXns m n).
Proof. by move=> c f g; rewrite !trXnsE !linearP. Qed.
Canonical trXns_linear := AddLinear trXns_is_linear.

Hypothesis H : n <= m.
Fact trXns_is_multiplicative : multiplicative (@trXns m n).
Proof.
split=> [f g|] /=; last exact trXns1.
rewrite /trXns /= mul_trpoly_val /=.
by rewrite -rmorphM /= trXn_trXn.
Qed.
Canonical trXns_multiplicative := AddRMorphism trXns_is_multiplicative.
Canonical trXns_lrmorphism := AddLRMorphism trXns_is_linear.

End TrXns.


Section TestTrXns.

Variable R : ringType.
Variables (m n p : nat).
Implicit Type (f g : {trpoly R m}).

(* Test *)
Example trpolys0 : trXns n (0 : {trpoly R m}) = 0.
Proof. by rewrite linear0. Qed.

Example trXn_trpoly1 : trXn n (trpoly (1 : {trpoly R m})) = 1.
Proof. by rewrite rmorph1. Qed.

Example trXnsZ c f : trXns n (c *: f) =  c *: (trXns n f).
Proof. by rewrite linearZ. Qed.

Example trXnsM f g : n <= m -> trXns n (f * g) = trXns n f * trXns n g.
Proof. by move=> H; rewrite rmorphM. Qed.

Example trXnsM12 (f g : {trpoly R 2}) :
  trXns 1 (f * g) =  (trXns 1 f) * (trXns 1 g).
Proof. by rewrite rmorphM. Qed.

End TestTrXns.


Section TruncPolyX.

Variable (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Lemma trpoly0X m : m = 0%N -> \Xo(m) = 0 :> {trpoly R m}.
Proof.
by move=> ->; rewrite (trpoly_is_cst \X) coef_trXn coefX /= trpolyC0.
Qed.

Lemma val_trpolySX m : trpoly (\Xo(m.+1)) = 'X%R :> {poly R}.
Proof.
apply/polyP => i.
by rewrite coef_trXn coefX; case: eqP => [->|] // _; rewrite if_same.
Qed.

Lemma val_trpolyX m : trpoly (\Xo(m)) = (m != 0%N)%:R *: 'X%R :> {poly R}.
Proof.
case: m => [|m]; first by rewrite trpoly0X /= ?scale0r.
by rewrite val_trpolySX /= scale1r.
Qed.

Lemma trXn_trpolyX m : @trXn R n.+1 (trpoly \Xo(m.+1)) = \X.
Proof. by apply trpoly_inj; rewrite !val_trpolySX. Qed.

Lemma trXns_trpolyX m : @trXns R _ n.+1 \Xo(m.+1) = \X.
Proof. exact: trXn_trpolyX. Qed.

Lemma commr_trpolyX f : GRing.comm f \X.
Proof.
apply/trpolyP => i _.
by rewrite !mul_trpoly_val /= trXn_mull trXn_mulr commr_polyX.
Qed.

Lemma coef_trpolyX f i : (\X : {trpoly R n.+1})`_i = (i == 1%N)%:R.
Proof. by rewrite coef_trpolyE val_trpolyX coefZ coefX mul1r. Qed.

Lemma coef_trpolyXM f i :
  (\X * f)`_i = if i == 0%N then 0 else if i <= n then f`_i.-1 else 0.
Proof. by rewrite !mul_trpoly_val /= trXn_mull coef_trXn coefXM; case: i. Qed.

Lemma coef_trpolyXnM f k i :
  (\X ^+ k * f)`_i = if i < k then 0 else if i <= n then f`_(i - k) else 0.
Proof.
elim: k i => [|k IHk] i.
  by rewrite expr0 ltn0 mul1r subn0 {1}coef_trpoly.
rewrite exprS -mulrA coef_trpolyXM {}IHk.
case: i => [|i]//=; rewrite ltnS subSS.
by case: (ltnP i n) => [/ltnW ->|]//; rewrite if_same.
Qed.

Lemma coef_trpolyXn i k :
  ((\X : {trpoly R n})^+ k)`_i = ((i <= n) && (i == k%N))%:R.
Proof.
rewrite -[_ ^+ k]mulr1 coef_trpolyXnM coef1 -/(leq _ _).
case: (altP (i =P k)) => [-> | Hneq]; first by rewrite ltnn leqnn; case: leqP.
case: (leqP i n) => _; last by rewrite if_same.
case: ltnP => //=.
by rewrite [i <= k]leq_eqVlt (negbTE Hneq) ltnNge => ->.
Qed.

Lemma trpoly_def f : f = \sum_(i < n.+1) f`_i *: \X ^+ i.
Proof.
apply/trpolyP => j le_jn; have:= le_jn; rewrite -ltnS => lt_jn1.
rewrite coeftr_sum /= (bigD1 (Ordinal lt_jn1)) //=.
rewrite coeftrZ coef_trpolyXn eqxx le_jn mulr1.
rewrite big1 ?addr0 // => [[i /= Hi]]; rewrite -val_eqE /= => Hneq.
by rewrite coeftrZ coef_trpolyXn eq_sym (negbTE Hneq) andbF mulr0.
Qed.

End TruncPolyX.


Section ConverseTruncPoly.

Variable (R : ringType) (n : nat).

Fact size_conv_subproof (f : {trpoly R n}) :
  size (map_poly (fun c : R => c : R^c) (trpoly f)) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_trpoly. Qed.
Definition conv_trpoly f : {trpoly R^c n} := Trpoly_of (size_conv_subproof f).

Fact size_iconv_subproof (f : {trpoly R^c n}) :
  size (map_poly (fun c : R^c => c : R) (trpoly f)) <= n.+1.
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
rewrite coefM_trpoly coef_map_id0 // coefMr_trpoly Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.
Lemma iconv_trpolyM f g :
  iconv_trpoly f * iconv_trpoly g = iconv_trpoly (g * f).
Proof.
apply/trpolyP => i Hi.
rewrite coefM_trpoly coef_map_id0 // coefMr_trpoly Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.

End ConverseTruncPoly.


Section TruncPolyTheoryComRing.

Variable (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact mul_trpolyC f g : f * g = g * f.
Proof. by rewrite !mul_trpoly_val mulrC. Qed.
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
    else - f`_0%N^-1 * (\sum_(i < m) f`_i.+1 * (inv_trpoly_rec f b (m - i.+1)%N))
  else f`_0%N^-1.
Definition inv_trpoly f : {trpoly R n} :=
  if unit_trpoly f then [trpoly i <= n => inv_trpoly_rec f i i] else f.

Lemma coef0_inv_trpoly f : unit_trpoly f -> (inv_trpoly f)`_0 = f`_0^-1.
Proof. by rewrite /inv_trpoly => ->; rewrite coef_trpoly_of_fun. Qed.

Lemma coefS_inv_trpoly f m :
  unit_trpoly f -> m < n ->
  (inv_trpoly f)`_m.+1 =
  - f`_0%N^-1 *
    (\sum_(i < m.+1) f`_i.+1 * (inv_trpoly f)`_(m - i)%N).
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
  by rewrite coef1 coef0_trpolyM coef0_inv_trpoly ?divrr.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/=.
case: (ltnP m.+1 n.+1) => Hmn; last first.
  by rewrite nth_default ?(leq_trans (size_trpoly _)).
rewrite coefM_trpoly -ltnS Hmn big_ord_recl [val ord0]/= subn0.
rewrite coefS_inv_trpoly // mulNr mulrN mulVKr // addrC.
apply/eqP; rewrite subr_eq0; apply/eqP.
by apply eq_bigr => [] [i] /=.
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
move=> [] /(congr1 (fun x : {trpoly _ _ } => x`_0)).
rewrite coef1 coef0_trpolyM => Hl.
move=>    /(congr1 (fun x : {trpoly _ _ } => x`_0)).
rewrite coef1 coef0_trpolyM => Hr.
by rewrite /unit_trpoly; apply/unitrP; exists g`_0.
Qed.

Definition trpoly_unitMixin :=
  UnitRingMixin mul_trpolyrV (@mul_trpolyVr _ _) unit_trpolyP (@inv_trpoly0id _ _).
Canonical trpoly_unitRingType :=
  Eval hnf in UnitRingType {trpoly R n} trpoly_unitMixin.

Lemma coef0_trpolyV f : f \is a GRing.unit -> f^-1`_0 = f`_0^-1.
Proof. exact: coef0_inv_trpoly. Qed.

Lemma unit_trpolyE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma trXn_unitE (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_trpolyE coef0_trXn. Qed.

Lemma coef_inv_trpoly f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_j.+1 * f^-1`_(i - j.+1)).
Proof.
move=> funit; case: ltnP => Hi.
  by rewrite -(trpolyK f^-1) coef_trXn leqNgt Hi.
case: i Hi => [|i] Hi; first by rewrite eq_refl coef0_trpolyV.
by rewrite coefS_inv_trpoly.
Qed.

Fact coef0_inv f : (f ^-1)`_0 = (f`_0)^-1.
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


Section MoreTruncPolyTheoryUnitRing.

Variable (R : unitRingType) (m n : nat).
Implicit Types (f g : {trpoly R n}).

Lemma trXns_unitE f :
  ((trXns m f) \is a GRing.unit) = (f`_0 \is a GRing.unit).
Proof. exact: trXn_unitE. Qed.

Lemma trXnsV f : m <= n -> trXns m (f^-1) = (trXns m f) ^-1.
Proof.
move=> leq_mn.
case (boolP (f`_0 \is a GRing.unit)) => f0U; first last.
  by rewrite !invr_out // unit_trpolyE ?coef0_trXn.
by rewrite rmorphV.
Qed.

Lemma trXnV f : m <= n -> trXn m (trpoly f^-1) = (trXn m (trpoly f)) ^-1.
Proof. move=> leq_mn; exact: trXnsV. Qed.

End MoreTruncPolyTheoryUnitRing.


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

Lemma trXn_modE m (p : {poly R}) : p %% 'X^ m.+1 = trpoly (trXn m p).
Proof. by apply/val_inj => /=; rewrite trXnE poly_modXn. Qed.

Fact trpoly_modp (n m : nat) (p : {poly R}) : n <= m ->
  trXn n (p %% 'X^m.+1) = trXn n p.
Proof. by move=> lt_nm; apply/val_inj; rewrite /= trXn_modE trXn_trXn. Qed.

Variable n : nat.
Implicit Types (f g : {trpoly R n}).

Fact mod_trpoly (m : nat) f : n <= m -> (trpoly f) %% 'X^m.+1 = (trpoly f).
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
rewrite coef_map /= !coefM_trpoly Hi rmorph_sum.
apply eq_bigr => [] [j]; rewrite /= ltnS => le_ji _.
by rewrite rmorphM !coef_map.
Qed.

Fact map_trpoly_is_additive : additive map_trpoly.
Proof. by move => x y; apply/trpoly_inj => /=; rewrite rmorphB. Qed.
Canonical map_trpoly_additive := Additive map_trpoly_is_additive.

Fact map_trpoly_is_multiplicative : multiplicative map_trpoly.
Proof.
split => [x y|]; first by rewrite map_trpolyM.
by apply/trpoly_inj => /=; rewrite rmorph1.
Qed.
Canonical map_trpoly_rmorphism := AddRMorphism map_trpoly_is_multiplicative.

Lemma map_trpolyZ (c : K) g : map_trpoly (c *: g) = (f c) *: (map_trpoly g).
Proof. by apply/trpolyP => i le_in; rewrite coef_trpolyE /= map_polyZ. Qed.
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
Proof. by apply/trpolyP => i le_in; rewrite !(coef_trXn, le_in, coef_map). Qed.

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
Proof.
by move=> x y /val_eqP/eqP /= /map_poly_injective H; apply trpoly_inj.
Qed.

Lemma map_trpoly_inj (K : fieldType) (L : ringType) n (f : {rmorphism K -> L}) :
  injective (@map_trpoly _ _ n f).
Proof. by move=> x y /val_eqP/eqP /= /map_poly_inj H; apply trpoly_inj. Qed.

Lemma trXns_map_poly (m n : nat) (K L : ringType)
      (f : {rmorphism K -> L}) (g : {trpoly K n}) :
  trXns m (map_trpoly f g) = map_trpoly f (trXns m g).
Proof. by apply/trpolyP=> i le_in; rewrite !(coef_map, coef_trXn) le_in. Qed.


Section IdFun.

Lemma map_poly_idfun (R : ringType) : map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma idfun_injective A : injective (@idfun A). Proof. done. Qed.
Canonical idfun_is_injmorphism (A : ringType) :=
    InjMorphism (@idfun_injective A).

End IdFun.

Lemma map_trpoly_idfun (K : fieldType) (m : nat) :
  map_trpoly [rmorphism of (@idfun K)] =1 @idfun {trpoly K m}.
Proof.
move=> f; apply/trpolyP => i le_in /=.
by rewrite coef_trpolyE /= map_poly_idfun.
Qed.


Section Coefficient01.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition coef0_eq0 : pred_class := fun f : {trpoly R n} => f`_0 == 0.
Definition coef0_eq1 : pred_class := fun f : {trpoly R n} => f`_0 == 1.

Lemma coef0_eq0E f : (f \in coef0_eq0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Lemma coef0_eq1E f : (f \in coef0_eq1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Fact c0_is_0_idealr : idealr_closed coef0_eq0.
Proof.
split => [|| a p q ]; rewrite ?coef0_eq0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefD q0_eq0 addr0 coef0_trpolyM p0_eq0 mulr0.
Qed.

Fact c0_is_0_key : pred_key coef0_eq0. Proof. by []. Qed.

Canonical c0_is_0_keyed := KeyedPred c0_is_0_key.
Canonical c0_is_0_opprPred := OpprPred c0_is_0_idealr.
Canonical c0_is_0_addrPred := AddrPred c0_is_0_idealr.
Canonical c0_is_0_zmodPred := ZmodPred c0_is_0_idealr.

Definition c0_is_0_ntideal := idealr_closed_nontrivial c0_is_0_idealr.
Canonical c0_is_0_ideal := MkIdeal c0_is_0_zmodPred c0_is_0_ntideal.

Lemma coef0_eq0Z f c : f \in coef0_eq0 -> c *: f \in coef0_eq0.
Proof. by move=> hf; rewrite -mulr_algl idealMr. Qed.

Lemma coef0_eq0X f i : f \in coef0_eq0 -> f ^+ i.+1 \in coef0_eq0.
Proof. by move=> hf; rewrite exprSr idealMr. Qed.

Lemma coef0_eq10 f : (f \in coef0_eq1) = ((1 - f) \in coef0_eq0).
Proof. by rewrite ?coef0_eq0E ?coef0_eq1E coefB coef1 subr_eq0 eq_sym. Qed.

Lemma coef0_eq01 f : (f \in coef0_eq0) = ((1 + f) \in coef0_eq1).
Proof. by rewrite coef0_eq10 -[RHS]rpredN !opprD !opprK addKr. Qed.

Lemma coef0_eq1_add01 f g :
  f \in coef0_eq0 -> g \in coef0_eq1 -> f + g \in coef0_eq1.
Proof.
rewrite coef0_eq0E !coef0_eq1E coefD => /eqP -> /eqP ->.
by rewrite add0r.
Qed.

Lemma trpolyX_in_coef0_eq0 : \X \in coef0_eq0.
Proof. by rewrite coef0_eq0E coef_trXn coefX. Qed.

(* tests *)
Example zero_in_coef0_eq0 : 0 \in coef0_eq0.
Proof. by rewrite rpred0. Qed.

Example coef0_eq0D f g :
    f \in coef0_eq0 -> g \in coef0_eq0 -> f + g \in coef0_eq0.
Proof. by move=> hf hg; rewrite rpredD. Qed.

Example coef0_eq0N f : f \in coef0_eq0 -> (-f) \in coef0_eq0.
Proof. by move=> hf; rewrite rpredN. Qed.


Fact mulr_closed_c0_is_1 : mulr_closed coef0_eq1.
Proof.
split=> [|x y]; rewrite !coef0_eq1E ?coefC //.
by rewrite coef0_trpolyM; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.
Fact c0_is_1_key : pred_key coef0_eq1. Proof. by []. Qed.
Canonical c0_is_1_keyed := KeyedPred c0_is_1_key.
Canonical c0_is_1_MulrPred := MulrPred mulr_closed_c0_is_1.

(* Tests *)
Example one_in_coef0_eq1 : 1 \in coef0_eq1.
Proof. by rewrite rpred1. Qed.

Example coef0_eq1M f g :
  f \in coef0_eq1 -> g \in coef0_eq1 -> f * g \in coef0_eq1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

End Coefficient01.
Arguments coef0_eq0 {R n}.
Arguments coef0_eq1 {R n}.

Lemma coef0_eq0_trXns (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
  (trXns m f \in coef0_eq0) = (f \in coef0_eq0).
Proof. by rewrite !coef0_eq0E coef0_trXn. Qed.

Lemma coef0_eq1_trXns (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
  (trXns m f \in coef0_eq1) = (f \in coef0_eq1).
Proof. by rewrite !coef0_eq1E coef0_trXn. Qed.


Section Coefficient01Unit.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact invr_closed_c0_is_1 : invr_closed (@coef0_eq1 R n).
Proof.
move=> f; rewrite !coef0_eq1E coef0_inv; move/eqP ->.
by rewrite invr1.
Qed.
Canonical c0_is_1_DivrPred := DivrPred invr_closed_c0_is_1.

Example coef0_eq1V f : f \in coef0_eq1 -> f^-1 \in coef0_eq1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Example coef0_eq1_div f g :
  f \in coef0_eq1 -> g \in coef0_eq1 -> f / g \in coef0_eq1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.

Lemma coef0_eq1_unit f : f \in coef0_eq1 -> f \is a GRing.unit.
Proof. by rewrite !coef0_eq1E unit_trpolyE => /eqP ->; apply unitr1. Qed.

End Coefficient01Unit.


Section Coefficient01IDomain.

Variables (R : idomainType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Fact c0_is_0_prime : prime_idealr_closed (@coef0_eq0 R n).
Proof.
by move => x y; rewrite -!topredE /= /coef0_eq0 coef0_trpolyM mulf_eq0.
Qed.
Canonical coef0_eq0_pideal := MkPrimeIdeal (c0_is_0_ideal R n) c0_is_0_prime.

Example coef0_eq0_prime_test f g :
  f * g \in coef0_eq0 -> (f \in coef0_eq0) || (g \in coef0_eq0).
Proof. by rewrite prime_idealrM. Qed.

End Coefficient01IDomain.


Section DivisionByX.

Variable R : ringType.

Definition mulfX m (f : {trpoly R m}) :=
  [trpoly i <= m.+1 => if i == 0%N then 0 else f`_i.-1].
Definition divfX m (f : {trpoly R m}) :=
  [trpoly i <= m.-1 => f`_i.+1].

Lemma coef_mulfX m (f : {trpoly R m}) i :
  (mulfX f)`_i = if i == 0%N then 0 else f`_i.-1.
Proof.
rewrite coef_trpoly_of_fun; case: i => //= i.
rewrite ltnS; case: leqP => // lt_mi.
by rewrite nth_default // (leq_trans (size_trpoly f) lt_mi).
Qed.
Lemma coef_divfX m (f : {trpoly R m}) i : (divfX f)`_i = f`_i.+1.
Proof.
rewrite coef_trpoly_of_fun; case: leqP => // Hi.
rewrite nth_default // (leq_trans (size_trpoly f)) //.
by move: Hi; case m.
Qed.

Lemma mulfXK m : cancel (@mulfX m) (@divfX m.+1).
Proof.
move=> p; apply/trpolyP => i Hi.
by rewrite coef_divfX coef_mulfX.
Qed.

Lemma divfXK m : {in coef0_eq0, cancel (@divfX m.+1) (@mulfX m)}.
Proof.
move=> p Hp.
by apply/trpolyP => [[|i]] Hi; rewrite coef_mulfX coef_divfX // (eqP Hp).
Qed.

Variable m : nat.
Implicit Type f : {trpoly R m}.

Lemma trXn_mulfXE f : trXn m (trpoly (mulfX f)) = \X * f.
Proof.
apply/trpolyP => i Hi.
by rewrite coef_trXn coef_mulfX coef_trpolyXM Hi.
Qed.

Lemma mulfXE f : mulfX f = \X * trXns m.+1 f.
Proof.
apply/trpolyP => i Hi.
rewrite coef_mulfX coef_trpolyXM coef_trXn Hi.
by case: i Hi => //= i /ltnW ->.
Qed.

Lemma trXns_mulfX f n :
  n <= m -> trXns n.+1 (mulfX f) = mulfX (trXns n f).
Proof.
move=> le_nm; apply/trpolyP => i le_in1.
rewrite coef_trXn !coef_mulfX le_in1.
by case: i le_in1 => //= i; rewrite ltnS coef_trXn => ->.
Qed.


Lemma coef_mulfX_exp_lt f i j : i < j -> (mulfX f ^+ j)`_i = 0.
Proof.
elim: j i => [|j IHj] i //; rewrite ltnS => le_ij.
rewrite exprS coefM_trpoly; case leqP => // _.
rewrite big_ord_recl big1 ?coef_mulfX ?mul0r ?add0r // => [[u /=]] lt_ui _.
rewrite {}IHj ?mulr0 // /bump /= add1n.
case: i lt_ui le_ij => // i _ lt_ij.
by rewrite subSS (leq_ltn_trans (leq_subr _ _) lt_ij).
Qed.

Lemma coef_mulfX_exp f i : i <= m.+1 -> (mulfX f ^+ i)`_i = (f ^+ i)`_0.
Proof.
elim: i => [|i IHi] lt_im1; first by rewrite !expr0 coef1.
rewrite exprS coefM_trpoly (leq_trans lt_im1 _) //.
rewrite big_ord_recl coef_mulfX mul0r add0r.
rewrite big_ord_recl coef_mulfX /= /bump /= add1n subSS subn0.
rewrite {}IHi ?(ltnW lt_im1) // -!/(_`_0).
rewrite -coef0_trpolyM ?rpredX // -exprS.
rewrite big1 ?addr0 // => [[j /= lt_ji]] _.
rewrite !add1n subSS coef_mulfX_exp_lt ?mulr0 //.
case: i lt_ji {lt_im1} => // i.
by rewrite !ltnS subSS leq_subr.
Qed.

End DivisionByX.

Lemma divfXE (K : idomainType) m :
  {in @coef0_eq0 K m, forall f, divfX f = trXn m.-1 (trpoly f %/ 'X)}.
Proof.
move=> f.
move/eqP/polyXP; rewrite Pdiv.IdomainUnit.dvdp_eq ?lead_coefX ?unitr1 //.
rewrite /divfX; move/eqP => h; apply/trpolyP => i Hi.
by rewrite coef_poly coef_trXn ltnS Hi coef_trpolyE [in LHS]h coefMX.
Qed.

Lemma map_trpoly_mulfX (K L : ringType) (f : {rmorphism K -> L})
  (m : nat) (g : {trpoly K m}) :
  map_trpoly f (mulfX g) = mulfX (map_trpoly f g).
Proof.
apply/trpolyP => i lt_im1.
rewrite !(coef_mulfX, coef_map, lt_im1).
by case: i {lt_im1}=> [|j]//=; rewrite rmorph0.
Qed.

Lemma map_trpoly_divfX (K L : ringType) (f : {rmorphism K -> L})
  (m : nat) (g : {trpoly K m}) :
  map_trpoly f (divfX g) = divfX (map_trpoly f g).
Proof.
apply/trpolyP => i lt_im1.
by rewrite !(coef_divfX, coef_map, lt_im1).
Qed.


Section Derivative.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Lemma deriv_trXn (p : {poly R}) :
  (trpoly (trXn n.+1 p))^`() = trpoly (trXn n (p^`())).
Proof.
apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv ltnS.
by case: leqP => //; rewrite mul0rn.
Qed.

Fact trXn_deriv (m : nat) (f : {trpoly R n}) : n <= m ->
  trpoly (trXn m (trpoly f)^`()) = (trpoly f)^`().
Proof.
move => le_nm; apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv.
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

Lemma val_deriv_trpoly f : trpoly (deriv_trpoly f) = (trpoly f)^`()%R.
Proof. by apply/polyP => i; rewrite coef_deriv_trpoly coef_deriv. Qed.

Lemma deriv_trpolyE f : deriv_trpoly f = trXn n.-1 (trpoly f)^`().
Proof. by rewrite -val_deriv_trpoly trpolyK. Qed.

Fact deriv_trpoly0 : (0 : {trpoly R n})^`() = 0.
Proof. by apply trpoly_inj; rewrite val_deriv_trpoly deriv0. Qed.

Lemma deriv_trpolyC (c : R) : c%:S^`() = 0.
Proof. by apply trpoly_inj; rewrite val_deriv_trpoly /= val_trpolyC derivC. Qed.

Lemma deriv_trpoly1 : 1^`() = 0.
Proof. by rewrite -trpolyC1 deriv_trpolyC. Qed.

Fact deriv_trpolyD f g : (f + g)^`() = f^`()%trpoly + g^`()%trpoly.
Proof.
apply/trpolyP => i le_in1.
by rewrite coefD !coef_poly ltnS le_in1 coefD -mulrnDl.
Qed.

Fact deriv_trpolyZ (c : R) f : (c *: f)^`() = c *: f^`()%trpoly.
Proof.
apply/trpolyP => i le_in1.
by rewrite !(coef_poly, coefZ) ltnS le_in1 mulrnAr.
Qed.

Fact deriv_trpoly_is_linear : linear deriv_trpoly.
Proof. by move => c f g; rewrite deriv_trpolyD deriv_trpolyZ. Qed.
Canonical deriv_trpoly_additive := Additive deriv_trpoly_is_linear.
Canonical deriv_trpoly_linear := Linear deriv_trpoly_is_linear.

(* Tests *)
Example test_deriv_trpoly0 : 0^`() = 0.
Proof. by rewrite linear0. Qed.

Example test_deriv_trpolyD f g :
  (f + g)^`() = f^`()%trpoly + g^`()%trpoly.
Proof. by rewrite linearD. Qed.

End Derivative.

Notation "f ^` () " := (deriv_trpoly f) : trpoly_scope.


Section MoreDerivative.

Variables (R : ringType).

Lemma deriv_trpolyX n : \Xo(n.+1)^`() = 1  :> {trpoly R n}.
Proof. by rewrite deriv_trpolyE val_trpolyX scale1r derivX trXn1. Qed.

Lemma deriv_trXns m n (p : {trpoly R m}) :
  (trXns n.+1 p)^`()%trpoly = trXns n (p^`())%trpoly.
Proof.
rewrite /trXns deriv_trpolyE deriv_trXn [n.+1.-1]/= trXn_trXn //.
by rewrite -val_deriv_trpoly.
Qed.

Lemma deriv_trpoly0p (f : {trpoly R 0}) : f^`() = 0.
Proof. by rewrite [f]trpoly_is_cst deriv_trpolyC. Qed.

Theorem derivM_trpoly n (f g : {trpoly R n}) :
  (f * g)^`() = f^`()%trpoly * (trXns n.-1 g) + (trXns n.-1 f) * g^`()%trpoly.
Proof.
move: f g; case: n => /= [f g | m f g].
  rewrite [f]trpoly_is_cst [g]trpoly_is_cst -trpolyCM !deriv_trpolyC.
  by rewrite mul0r mulr0 addr0.
apply/trpoly_inj; rewrite !deriv_trpolyE deriv_trXn /=.
by rewrite trXn_trXn // derivM rmorphD !rmorphM.
Qed.

End MoreDerivative.


Section DerivativeComRing.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).


Theorem derivX_trpoly f k :
  (f ^+ k)^`() = (trXns n.-1 f) ^+ (k.-1) * (f^`())%trpoly *+ k.
Proof.
case: k; first by rewrite !expr0 deriv_trpoly1 mulr0n.
elim=> [|k IHk] /=; first by rewrite !expr1 expr0 mul1r mulr1n.
rewrite exprS derivM_trpoly {}IHk /=.
rewrite -mulrnAr mulrA -exprS mulrC rmorphX ?leq_pred //= => _.
by rewrite -mulrDr -mulrS -mulrnAr.
Qed.

Theorem derivX_trpoly_bis f k :
  (f ^+ k)^`() = (f^`())%trpoly * (trXns n.-1 f) ^+ (k.-1) *+ k.
Proof.
case: k; first by rewrite !expr0 deriv_trpoly1 mulr0n.
elim=> [|k IHk] /=; first by rewrite !expr1 expr0 mulr1 mulr1n.
rewrite exprS derivM_trpoly {}IHk /=.
rewrite -mulrnAr mulrA [_ * _^`()%trpoly]mulrC.
by rewrite mulrnAr -mulrA -exprS rmorphX ?leq_pred.
Qed.

End DerivativeComRing.


Section DerivativeUnitRing.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

(* Noncommutative version *)
Theorem derivV_trpoly_unit f :
  f \is a GRing.unit ->
  (f ^-1)^`() = - trXns n.-1 (f^-1) * (f^`()%trpoly) * trXns n.-1 (f^-1).
Proof.
move => fU.
have:= erefl (f / f); rewrite {2}divrr //.
move/(congr1 (@deriv_trpoly R n)).
rewrite derivM_trpoly -trpolyC1 deriv_trpolyC.
(* Coq is confused with the pattern matching :-( ?? Let's help him ! *)
move/eqP; rewrite addrC; set X := (X in X + _); rewrite (addr_eq0 X _) {}/X.
move/eqP/(congr1 (fun x => (trXns n.-1 f ^-1) * x)).
rewrite {1}trXnsV ?leq_pred // mulKr ?(mulrN, mulNr, mulrA) //.
by rewrite unit_trpolyE coef0_trXn.
Qed.

End DerivativeUnitRing.


Section DerivativeComUnitRing.

Variables (R : comUnitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Theorem derivV_trpoly f :
  f \is a GRing.unit -> (f ^-1)^`() = - (f^`()%trpoly) / trXns n.-1 (f ^+ 2).
Proof.
move=> fU.
rewrite derivV_trpoly_unit // -mulrA mulrC -mulrA !mulrN mulNr.
rewrite trXnsV ?leq_pred // -invrM ?unit_trpolyE ?coef0_trXn //.
by rewrite -{1}rmorphM ?leq_pred.
Qed.

Theorem deriv_div_trpoly f g :
  g \is a GRing.unit ->
  (f / g)^`() = (f^`()%trpoly * trXns n.-1 g - trXns n.-1 f * g^`()%trpoly)
                                                    / (trXns n.-1 (g ^+ 2)).
Proof.
move => fU.
rewrite derivM_trpoly derivV_trpoly // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
rewrite trXnsV ?leq_pred // expr2 ?leq_pred //.
rewrite rmorphM ?leq_pred //= => Hn.
by rewrite invrM ?mulrA ?divrr ?div1r // trXns_unitE.
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

Lemma size_prim_leq f : size (prim (trpoly f)) <= n.+2.
Proof.
apply: (leq_trans (size_poly _ _) _); rewrite ltnS.
exact: size_trpoly.
Qed.
Definition prim_trpoly f := Trpoly_of (size_prim_leq f).

Lemma coef_prim_trpoly f i : (prim_trpoly f)`_i = (prim (trpoly f))`_i.
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

Lemma coefX_eq0 n m p : p`_0 = 0 -> n < m -> (p ^+ m)`_n = 0.
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

Lemma trXnX_eq0 n m p : p`_0 = 0 -> n < m -> trXn n (p ^+ m) = 0.
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

Lemma coefX_trpoly_eq0 n m i :
  i < m -> {in coef0_eq0, forall f : {trpoly R n}, (f ^+ m)`_i = 0}.
Proof.
move=> lt_im f; rewrite coef0_eq0E => /eqP/coefX_eq0/(_ lt_im).
by rewrite coef_trpolyE !exp_trpoly_val coef_trXn => ->; rewrite if_same.
Qed.

Lemma trpolyX_eq0 (n m : nat) :
  n < m -> {in coef0_eq0, forall f : {trpoly R n}, f ^+ m = 0}.
Proof.
move=> le_nm f /coefX_trpoly_eq0 H0.
apply/trpolyP => i le_in.
by rewrite coef0 H0 // (leq_ltn_trans le_in le_nm).
Qed.

Lemma trpolyMX_eq0 n i j : n < i + j ->
  {in @coef0_eq0 R n &, forall f g, f ^+ i * g ^+ j = 0}.
Proof.
move=> lt_n_addij f g f0 g0.
apply trpoly_inj.
rewrite mul_trpoly_val !exp_trpoly_val trXn_mul.
by rewrite trXnMX_eq0 //= -/(_`_0) ?(eqP f0) ?(eqP g0).
Qed.

End MoreExpPoly.


Section MoreCompPoly.

Variable (R : comRingType).
Implicit Type (p q : {poly R}).

Lemma trXn_comp_polyr n p q :
  trXn n (p \Po q) = trXn n (p \Po (trpoly (trXn n q))).
Proof.
apply/trXnP => i le_in.
rewrite !coef_comp_poly; apply eq_bigr => j _; congr (_ * _).
have /= := (congr1 (fun x => (trpoly x)`_i) (exp_trpoly_val (trXn n q) j)).
rewrite !coef_trXn le_in => <-.
by rewrite -rmorphX coef_trXn le_in.
Qed.

Lemma trXn_comp_polyl n p q :
  q`_0 = 0 -> trXn n (p \Po q) = trXn n ((trpoly (trXn n p)) \Po q).
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
  if f \in coef0_eq0
  then trXn m (trpoly g \Po trpoly f)
  else (g`_0%N)%:S.  (* avoid particular cases (e.g. associatvity) *)

Local Notation "f \So g" := (comp_trpoly g f) : trpoly_scope.


Lemma comp_trpoly_coef0_neq0 m (f g : {trpoly R m}) :
  g \notin coef0_eq0 -> f \So g = (f`_0%N)%:S.
Proof. by move/negbTE => p0_neq0; rewrite /comp_trpoly p0_neq0. Qed.

Lemma comp_trpoly_coef0_eq0 m (f g : {trpoly R m}) :
  g \in coef0_eq0 -> f \So g = trXn m (trpoly f \Po trpoly g).
Proof. by move => f0_eq0 ; rewrite /comp_trpoly f0_eq0. Qed.

Lemma coef0_comp_trpoly f g : (f \So g)`_0 = f`_0.
Proof.
rewrite /comp_trpoly; case: (boolP (_ \in _)); last by rewrite coef_trpolyC.
rewrite coef0_eq0E coef_trXn {-2}[0%N]lock /= -lock => /eqP.
by rewrite -!horner_coef0 horner_comp => ->.
Qed.

Lemma coef_comp_trpoly k f g :
  g \in coef0_eq0 -> (f \So g)`_k = \sum_(i < k.+1) f`_i * (g ^+ i)`_k.
Proof.
move=> g0; rewrite (comp_trpoly_coef0_eq0 _ g0).
rewrite coef_trXn; case: leqP => [le_kn | lt_nk].
- rewrite coef_comp_poly.
  have co_is0 i : minn (size f) k.+1 <= i -> f`_i * (g ^+ i)`_k = 0.
    rewrite geq_min => /orP [/(nth_default _) ->| lt_ki]; first by rewrite mul0r.
    rewrite !coef_trpolyE !exp_trpoly_val coef_trXn le_kn.
    by rewrite coefX_eq0 ?mulr0 ?(eqP g0).
  rewrite [RHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
  rewrite [LHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
  rewrite [X in _ + X]big1 ?addr0; first last.
    move=> [i /=] _; rewrite -leqNgt => /co_is0 /=.
    by rewrite !coef_trpolyE !exp_trpoly_val coef_trXn le_kn.
  rewrite [X in _ + X]big1 ?addr0; first last.
    by move=> [i /=] _; rewrite -leqNgt => /co_is0.
  rewrite -(big_ord_widen _ (fun i => f`_i * (g ^+ i)`_k)) ?geq_minr //.
  rewrite -(big_ord_widen _ (fun i => f`_i * (trpoly g ^+ i)`_k)) ?geq_minl //.
  by apply eq_bigr => i _; rewrite !coef_trpolyE !exp_trpoly_val coef_trXn le_kn.
- apply/esym/big1 => [[l /=]]; rewrite ltnS => Hl _.
  by  rewrite [_`_k]coef_trpoly /= leqNgt lt_nk /= mulr0.
Qed.

Lemma trXns_comp m f g :
  m <= n -> trXns m (f \So g) = (trXns m f) \So (trXns m g).
Proof.
case (boolP (g \in coef0_eq0)) => [g0_eq0 | g0_neq0] le_mn.
- rewrite !comp_trpoly_coef0_eq0 ?coef0_eq0_trXns //.
  rewrite /trXns -trXn_comp_polyr -trXn_comp_polyl ?(eqP g0_eq0) //=.
  by rewrite trXn_trXn.
- rewrite !comp_trpoly_coef0_neq0 ?coef0_eq0_trXns //.
  by rewrite trXnsC coef_trXn.
Qed.

Lemma coef0_eq0_comp f g : (f \So g \in coef0_eq0) = (f \in coef0_eq0).
Proof. by rewrite !coef0_eq0E coef0_comp_trpoly. Qed.

Lemma coef0_eq1_comp f g : (f \So g \in coef0_eq1) = (f \in coef0_eq1).
Proof. by rewrite !coef0_eq1E coef0_comp_trpoly. Qed.

Lemma comp_trpoly0r f : f \So 0 = (f`_0)%:S.
Proof.
rewrite comp_trpoly_coef0_eq0 ?rpred0 // comp_poly0r.
by rewrite -trpolyCE -coef_trpolyE.
Qed.

Lemma comp_trpoly0 f : 0 \So f = 0.
Proof.
case (boolP (f \in coef0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_trpoly_coef0_eq0 // comp_poly0 rmorph0.
- by rewrite comp_trpoly_coef0_neq0 // coef0 trpolyC0.
Qed.

Lemma comp_trpolyC f (c : R) : c%:S \So f = c%:S.
Proof.
case (boolP (f \in coef0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_trpoly_coef0_eq0 //= val_trpolyC comp_polyC -trpolyCE.
- by rewrite comp_trpoly_coef0_neq0 ?coef_trpolyC.
Qed.

Lemma comp_trpoly1 f : 1 \So f = 1.
Proof. by rewrite -trpolyC1 comp_trpolyC. Qed.

Lemma comp_trpolyCf f (c : R) : f \So (c%:S) = (f`_0)%:S.
Proof.
have [->| c_neq0] := eqVneq c 0.
  by rewrite trpolyC0 comp_trpoly0r.
by rewrite comp_trpoly_coef0_neq0 // coef0_eq0E coef_trpolyC.
Qed.


Fact comp_trpoly_is_additive :
  {in @coef0_eq0 R n, forall f, additive (comp_trpoly f)}.
Proof.
by move=> f f0_eq0 u v; rewrite !comp_trpoly_coef0_eq0 // !rmorphB.
Qed.
Canonical comp_trpoly_additive f (Hf : f \in coef0_eq0) :=
  Additive (comp_trpoly_is_additive Hf).

Fact comp_trpoly_is_linear :
  {in @coef0_eq0 R n, forall f, linear (comp_trpoly f)}.
Proof.
move=> f f0_eq0 a q r.
by rewrite !comp_trpoly_coef0_eq0 // !rmorphD /= !linearZ.
Qed.
Canonical comp_trpoly_linear f (Hf : f \in coef0_eq0) :=
  Linear (comp_trpoly_is_linear Hf).

Fact comp_trpoly_is_rmorphism :
  {in @coef0_eq0 R n, forall f, rmorphism (comp_trpoly f)}.
Proof.
move=> f f0_eq0.
split; first exact: comp_trpoly_is_additive.
split => [g1 g2|]; last exact: comp_trpoly1.
rewrite /comp_trpoly f0_eq0 //.
rewrite mul_trpoly_val /= -trXn_comp_polyl ?(eqP f0_eq0) //.
rewrite rmorphM /= -trXn_mul /=.
by rewrite -[RHS]trpolyK mul_trpoly_val /= trXn_trXn.
Qed.
Canonical comp_trpoly_rmorphism f (Hf : f \in coef0_eq0) :=
  RMorphism (comp_trpoly_is_rmorphism Hf).


Lemma comp_trpolyXr f : n != 0%N -> f \So \X = f.
Proof.
rewrite comp_trpoly_coef0_eq0 ?trpolyX_in_coef0_eq0 //.
case: n f => // m f _.
by rewrite val_trpolySX comp_polyXr trpolyK.
Qed.

Lemma comp_trpolyX : n != 0%N -> {in coef0_eq0, forall f, \X \So f = f}.
Proof.
move=> Hn f /comp_trpoly_coef0_eq0 ->.
case: n f Hn => // m f _.
by rewrite val_trpolySX comp_polyX trpolyK.
Qed.

Lemma comp_trpolyXn i : n != 0%N ->
                        {in coef0_eq0, forall f, \X^+i \So f = f^+ i}.
Proof.
move=> Hn f Hf; elim: i => [|i IHi]; first by rewrite !expr0 comp_trpoly1.
by rewrite !exprS rmorphM /= IHi comp_trpolyX.
Qed.

Lemma coef_comp_trpoly_cX f c i :
  n != 0%N -> (f \So (c *: \X))`_i = c ^+ i * f`_i.
Proof.
move=> n_neq0.
case: (leqP i n) => [le_in | lt_ni]; first last.
  rewrite coef_trpoly leqNgt lt_ni /= nth_default ?mulr0 //.
  exact: (leq_trans (size_trpoly f) lt_ni).
rewrite -coef_comp_poly_cX.
rewrite comp_trpoly_coef0_eq0 ?coef0_eq0Z ?trpolyX_in_coef0_eq0 //.
by rewrite coef_trXn le_in linearZ /= val_trpolyX n_neq0 scale1r.
Qed.

Lemma comp_trpolyA f g h : f \So (g \So h) = (f \So g) \So h.
Proof.
case (boolP (h \in coef0_eq0)) => [h0_eq0 | h0_neq0]; first last.
  rewrite !(comp_trpoly_coef0_neq0 _ h0_neq0).
  by rewrite comp_trpolyCf coef0_comp_trpoly.
case (boolP (g \in coef0_eq0)) => [g0_eq0 | g0_neq0]; first last.
  by rewrite !(comp_trpoly_coef0_neq0 f) ?comp_trpolyC // coef0_eq0_comp.
rewrite comp_trpoly_coef0_eq0 ?coef0_eq0_comp //.
rewrite !comp_trpoly_coef0_eq0 //.
rewrite -trXn_comp_polyr comp_polyA trXn_comp_polyl //.
by move: h0_eq0; rewrite coef0_eq0E => /eqP.
Qed.

End Composition.

Notation "f \So g" := (comp_trpoly g f) : trpoly_scope.


Section Lagrange.

Variables R : comUnitRingType.
Variable n : nat.


Section LagrangeFixPoint.

Variable g : {trpoly R n}.
Hypothesis gU : g \is a GRing.unit.


Fixpoint lagrfix_rec o : {trpoly R o} :=
  if o is o'.+1 then mulfX ((trXns o' g) \So (lagrfix_rec o')) else 0.
Definition lagrfix := lagrfix_rec n.+1.

Lemma coef0_eq0_lagrfix_rec o : lagrfix_rec o \in coef0_eq0.
Proof. by rewrite coef0_eq0E; case: o => [|o]; rewrite ?coef0 ?coef_poly. Qed.
Lemma coef0_eq0_lagrfix : lagrfix \in coef0_eq0.
Proof. exact: coef0_eq0_lagrfix_rec. Qed.

Lemma lagrfixP : lagrfix = mulfX (g \So trXns n lagrfix).
Proof.
rewrite /lagrfix.
suff rec o : o <= n ->
     lagrfix_rec o.+1 = mulfX (trXns o g \So trXns o (lagrfix_rec o.+1)).
  by rewrite [LHS](rec n (leqnn n)) trXns_id.
elim: o => [_ | o IHo /ltnW{}/IHo IHo]; apply trpolyP => i.
  case: i => [_|i]; first by rewrite /= -!/(_`_0) !coef_poly eqxx.
  rewrite ltnS leqn0 => /eqP ->.
  rewrite !coef_poly /= -!/(_`_0).
  by rewrite comp_trpoly0r !coef_trpolyC coef0_comp_trpoly eqxx coef_trXn leqnn.
case: i => [_|i]; first by rewrite /= -!/(_`_0) !coef_poly eqxx.
rewrite ltnS => le_in /=.
rewrite -!/(_`_ i.+1) !coef_poly !ltnS le_in /= -/(lagrfix_rec o.+1).
have lag0 := coef0_eq0_lagrfix_rec o.+1.
move: (lagrfix_rec o.+1) => LR in IHo lag0 *.
have Xlag0 : trXns o.+1 (mulfX (trXns o.+1 g \So LR)) \in coef0_eq0.
  by rewrite coef0_eq0E coef_trXn coef_poly.
rewrite !coef_comp_trpoly //; apply eq_bigr => k _; congr (_ * _).
rewrite {}[in LHS]IHo -rmorphX coef_trXn le_in.
set X :=  (_ ^+ k in RHS); have -> : X`_i = (trXns o.+1 X)`_i.
  by rewrite {}/X coef_trXn le_in.
rewrite {}/X rmorphX /= trXns_mulfX // trXns_comp; last exact: leqnSn.
by rewrite trXns_trXns.
Qed.

Lemma lagrfix_divP : divfX lagrfix = g \So trXns n lagrfix.
Proof. by rewrite {1}lagrfixP mulfXK. Qed.
Lemma divfX_lagrfix_unit : divfX lagrfix \is a GRing.unit.
Proof.
by rewrite lagrfix_divP unit_trpolyE coef0_comp_trpoly -unit_trpolyE.
Qed.

Lemma lagrfix_invPr : (mulfX g^-1) \So lagrfix = \X.
Proof.
have lag0 := coef0_eq0_lagrfix.
have tlag0 : trXns n lagrfix \in coef0_eq0.
  by rewrite coef0_eq0_trXns coef0_eq0_lagrfix.
rewrite mulfXE rmorphM /= comp_trpolyX //.
rewrite {1}lagrfixP mulfXE -mulrA -trXn_mulfXE.
rewrite -[LHS]/(trXns _ _) trXns_mulfX //.
rewrite trXnsM // trXns_trXns // [X in _ * X]trXns_comp //.
rewrite trXns_trXns // !trXns_id.
rewrite rmorphV //= divrr ?mulfXE ?trXns1 ?mulr1 //.
by rewrite -lagrfix_divP divfX_lagrfix_unit.
Qed.

End LagrangeFixPoint.

Implicit Types (f g : {trpoly R n.+1}).

Definition lagrunit f := (f \in coef0_eq0) && (divfX f \is a GRing.unit).
Definition lagrinv f := lagrfix (divfX f)^-1.

Lemma coef1_comp_trpoly f g :
  f \in coef0_eq0 -> g \in coef0_eq0 -> (f \So g)`_1 = f`_1 * g`_1.
Proof.
move=> f0 g0.
rewrite coef_comp_trpoly // big_ord_recl (eqP f0) mul0r add0r.
by rewrite big_ord_recl /= -!/(_`_ 1) big_ord0 /bump /= -!/(_`_ 1) !add1n addr0.
Qed.

Lemma divfX_unitE f : (divfX f \is a GRing.unit) = (f`_1 \is a GRing.unit).
Proof. by rewrite unit_trpolyE coef_divfX. Qed.

Lemma lagrunit_comp : {in lagrunit &, forall f g, lagrunit (f \So g) }.
Proof.
rewrite /lagrunit => f g /andP [f0 f1] /andP [g0 g1].
rewrite coef0_eq0_comp f0 /=.
rewrite unit_trpolyE coef_divfX /= -/(_`_1).
by rewrite coef1_comp_trpoly // unitrM -!divfX_unitE f1 g1.
Qed.

Lemma lagrunitV : {in lagrunit, forall f, lagrunit (lagrinv f) }.
Proof.
rewrite /lagrunit => f /andP [H0 H1].
by rewrite coef0_eq0_lagrfix divfX_lagrfix_unit // unitrV.
Qed.

Lemma lagrinvPr : {in lagrunit, forall f, f \So (lagrinv f) = \X }.
Proof.
rewrite /lagrinv/lagrunit => f /andP [H0 H1].
have /lagrfix_invPr : (divfX f)^-1 \is a GRing.unit by rewrite unitrV.
by rewrite invrK divfXK.
Qed.

Lemma lagrinvPl : {in lagrunit, forall f, (lagrinv f) \So f = \X }.
Proof.
move=> f Hf.
(** Standard group theoretic argument: right inverse is inverse *)
have idemp_neutral g : lagrunit g -> g \So g = g -> g = \X.
  move=> Hinv Hid; rewrite -(comp_trpolyXr g) // -(lagrinvPr Hinv).
  by rewrite comp_trpolyA {}Hid.
apply idemp_neutral; first exact: lagrunit_comp (lagrunitV Hf) Hf.
rewrite comp_trpolyA -[X in (X \So f)]comp_trpolyA lagrinvPr //.
by rewrite comp_trpolyXr.
Qed.

Lemma lagrfix_invPl :
  {in GRing.unit, forall g : {trpoly R n}, lagrfix g \So (mulfX g^-1) = \X}.
Proof.
move=> g gU.
have -> : lagrfix g = lagrinv (mulfX g^-1) by rewrite /lagrinv mulfXK invrK.
apply: lagrinvPl.
rewrite /lagrunit unfold_in coef0_eq0E coef_mulfX /= eqxx /=.
by rewrite divfX_unitE coef_mulfX /= -/(_`_0) -unit_trpolyE unitrV.
Qed.

End Lagrange.


Section LagrangeTheorem.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Variable n : nat.

Theorem Lagrange_BürmannXn (g : {trpoly R n.+1}) i k :
  g \in GRing.unit ->
  k <= i <= n.+2 -> ((lagrfix g) ^+ k)`_i *+ i = (g ^+ i)`_(i - k) *+ k.
Proof.
move=> gU.
case: k i=> [|k] [|i]; rewrite ?(expr0, subn0, coef1, mulr0n, mul0rn) //.
rewrite subSS !ltnS => /andP [le_ki le_in].
have Xg0 : mulfX g^-1 \in coef0_eq0 by rewrite coef0_eq0E coef_mulfX.
have:= congr1 (fun s => s ^+ k.+1) (lagrfix_invPl gU).
rewrite -rmorphX /= {1}(trpoly_def (lagrfix g ^+ k.+1)) rmorph_sum /=.
move HLGR : (lagrfix g ^+ k.+1) => LGR.
move=> /(congr1 (@deriv_trpoly _ _)); rewrite raddf_sum /=.
rewrite derivX_trpoly deriv_trpolyX mulr1 /= trXns_trpolyX.
move=> /(congr1 (fun s => (s * g ^+ i.+1)`_i)).
rewrite mulrnAl -mulrnAr coef_trpolyXnM ltnNge le_ki le_in /=.
rewrite coeftrMn /= => <-.
rewrite mulr_suml coeftr_sum -/(_`_i.+1).
have Hi : i.+1 < n.+3 by rewrite ltnS (leq_ltn_trans le_in).
rewrite (bigD1 (Ordinal Hi)) //= -/(_`_i.+1).
move: (LGR`_i.+1) => co.
rewrite !linearZ /= -scalerAl coeftrZ rmorphX /= comp_trpolyX //.
rewrite derivX_trpoly /= !mulrnAl coeftrMn /= mulrnAr -mulrnAl.
rewrite -mulrA coefM_trpoly le_in big_ord_recr /=.
rewrite coef_trXn subnn leq0n coef0M.
rewrite coef_trpoly_of_fun coef_mulfX /= -!/(_`_0) mulr1n.
rewrite {2}exprS coef0_trpolyM [g^-1`_0 * _]mulrA coef0_trpolyV //.
rewrite mulVr -?unit_trpolyE // mul1r.
rewrite -rmorphX /= coef_trXn le_in -!/(_`_0).
rewrite coef_mulfX_exp ?(leq_trans le_in) //.
rewrite -coef0_trpolyM exprVn mulVr ?rpredX // coef1 /=.
rewrite !big1 ?add0r ?addr0 ?mulr1 //; first last.
  move=> [j /= lt_ji] _.
  rewrite coef_trXn (leq_trans (ltnW lt_ji) le_in).
  by rewrite coef_mulfX_exp_lt // mul0r.
move=> [j Hj]; rewrite -val_eqE /= {Hi} => Hneq.
rewrite !linearZ /= -scalerAl coeftrZ rmorphX /= comp_trpolyX //.
rewrite [X in _ * X](_ : _ = 0) ?mulr0 // {LGR HLGR k le_ki}.

(** TODO Simplify from here *)
rewrite derivX_trpoly /= mulfXE.
rewrite derivM_trpoly deriv_trpolyX mul1r /= deriv_trXns.
rewrite trXns_trpolyX trXns_trXns ?ltnS // trXns_id.
rewrite -[X in _ + X]mulfXE.
rewrite -rmorphX /= exprMn_comm; last exact: (commr_sym (commr_trpolyX _)).
rewrite !rmorphM !rmorphX /= trXns_trpolyX trXns_trXns // trXns_id.
rewrite mulrnAl -!mulrA coeftrMn /= coef_trpolyXnM le_in.
case: j Hneq Hj => // j /=; rewrite eqSS !ltnS => Hij le_jn1.
case ltnP => /= [_| le_ji]; first by rewrite mul0rn.
have {Hij le_ji} lt_ji : j < i by rewrite ltn_neqAle Hij le_ji.
rewrite [X in X *+ _](_ : _ = 0) ?mul0rn //.
rewrite mulrC -mulrA exprVn -exprB ?(leq_trans (ltnW lt_ji)) //.
rewrite (subSn (ltnW _)) // exprS mulrA mulrDl mulVr //.
rewrite derivV_trpoly // /= mulfXE mulNr raddfN mulrN mulNr /= -mulfXE.
have -> : mulfX ((g^`())%trpoly / trXns n (g ^+ 2)) =
          mulfX (g^`())%trpoly / g ^+ 2.
  apply/trpolyP => l Hl; rewrite /= in Hl.
  rewrite coef_mulfX !coefM_trpoly.
  case: l Hl => [_|l].
    by rewrite [LHS]/= big_ord_recl big_ord0 addr0 coef_mulfX mul0r.
  rewrite ltnS => Hl; rewrite Hl [_.+1.-1]/= (_ : _.+1 == 0%N = false) //.
  rewrite [RHS]big_ord_recl coef_mulfX mul0r add0r.
  apply eq_bigr => m _.
  rewrite [val (lift _ _)]/= /bump add1n subSS coef_mulfX.
  rewrite (_ : _.+1 == 0%N = false) //; congr (_ * _).
  by rewrite -trXnsV // coef_trXn (leq_trans (leq_subr _ _) _).
rewrite exprS expr1 invrM // -!mulrA mulVr // mulr1.
move: lt_ji; rewrite -subn_gt0.
case: (i - j)%N (leq_subr j i) => // d lt_di _ {j le_jn1}.
rewrite exprS mulrA mulrDl mul1r mulNr divrK //.
rewrite mulrDl -exprS mulNr coeftrB /= -!/(_`_d.+1).
apply/eqP; rewrite subr_eq0; apply/eqP.
apply (mulIr (nat_unit d)); rewrite mulr_natr -coef_deriv_trpoly.
rewrite derivX_trpoly coeftrMn -mulr_natr; congr (_ * _).
have lt_dn1 := leq_trans lt_di le_in.
rewrite mulrC !coefM_trpoly -ltnS lt_dn1.
rewrite [RHS]big_ord_recr subnn coef_mulfX !mulr0 /= addr0.
apply eq_bigr => [[j /=]]; rewrite ltnS => Hj _; congr (_ * _).
  by rewrite -rmorphX coef_trXn (leq_trans Hj) // -ltnS .
rewrite !coef_poly subSn //= !ltnS.
by case: leqP.
Qed.


Theorem Lagrange_Bürmann (g : {trpoly R n.+1}) (h : {trpoly R n.+2}) i  :
  g \in GRing.unit ->
  (h \So (lagrfix g))`_i.+1 = ((h^`()%trpoly * g ^+ i.+1)`_i) / i.+1%:R.
Proof.
move=> gU.
have lg0 := coef0_eq0_lagrfix g.
(* We argue by linearity from the previous statement *)
rewrite (trpoly_def h) !(raddf_sum, mulr_suml, coeftr_sum).
apply eq_bigr => [[k /=]]; rewrite ltnS => le_kn2 _.
rewrite !linearZ /= -/(_`_i.+1) -scalerAl !coeftrZ -mulrA; congr (_ * _).
case: k le_kn2 => [_|k lt_kn2].
  (* When k = 0 the result is trivial *)
  by rewrite expr0 comp_trpoly1 coef1 deriv_trpoly1 mul0r coef0 mul0r.
rewrite rmorphX /= comp_trpolyX // -/(_`_i.+1).
rewrite [LHS]coef_trpoly [in RHS]coef_trpoly ltnS.
case: leqP => [le_in1|_]; last by rewrite mul0r.
case: (ltnP i k) => [lt_ik | le_ki].
  (* If i < k both side vanishes *)
  rewrite coefX_trpoly_eq0 ?ltnS //.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  rewrite coefM_trpoly le_in1; apply big1 => [[j /=]]; rewrite ltnS => le_ji _.
  rewrite coef_deriv_trpoly.
  rewrite coef_trpolyXn eqSS (ltn_eqF (leq_ltn_trans le_ji lt_ik)).
  by rewrite andbF mul0rn mul0r.
(* Else we conclude by the previous theorem *)
apply (mulIr (nat_unit i)); rewrite divrK // mulr_natr.
rewrite Lagrange_BürmannXn //; last by rewrite !ltnS le_ki le_in1.
rewrite subSS derivX_trpoly /= trXns_trpolyX deriv_trpolyX mulr1.
rewrite mulrnAl -mulrnAr coef_trpolyXnM le_in1 ltnNge le_ki /=.
by rewrite coeftrMn.
Qed.

End LagrangeTheorem.


Section DerivComp.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).


Theorem deriv_trpoly_comp f g :
  f \in coef0_eq0 ->
  (g \So f)^`() = (g^`()%trpoly \So (trXns n.-1 f)) * f^`()%trpoly.
Proof.
rewrite !deriv_trpolyE //.
move: f g; case: n => [|m] f g f0_eq0.
  rewrite [f]trpoly_is_cst [g]trpoly_is_cst.
  rewrite /trXns comp_trpolyC.
  by rewrite !val_trpolyC !derivC trXn0 mulr0.
rewrite -[RHS]trpolyK [m.+1.-1]/=.
rewrite /= !comp_trpoly_coef0_eq0 ?coef0_eq0_trXns //.
rewrite deriv_trXn !trXn_trXn // deriv_comp.
rewrite -trXn_mul /=; congr (trXn _ (_ * _)).
by rewrite -trXn_comp_polyr trXn_comp_polyl ?(eqP f0_eq0).
Qed.

End DerivComp.

Section ExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition exp f : {trpoly R n} :=
  if f \notin coef0_eq0 then 0 else
  \sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i.

Definition log f : {trpoly R n} :=
  if f \notin coef0_eq1 then 0 else
  - \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i.

Definition expr_trpoly (c : R) f := exp (c *: log f).

Lemma exp_coef0_eq0 f : f \in coef0_eq0 ->
  exp f = \sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i.
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_eq0_val f : f \in coef0_eq0 ->
  exp f = trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (trpoly f) ^+i).
Proof.
rewrite /exp => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]trpolyK !linearZ /= exp_trpoly_val trXn_trXn.
Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_eq0 -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0 : exp (0 : {trpoly R n}) = 1.
Proof.
apply/trpolyP => i le_in.
rewrite exp_coef0_eq0 ?rpred0 // !coeftr_sum /=.
rewrite big_ord_recl /= fact0 invr1 expr0 alg_trpolyC trpolyC1.
rewrite big1 ?addr0 // => [] [j ] _ _ /=.
by rewrite /bump /= add1n expr0n /= scaler0 coef0.
Qed.

Lemma expC (c : R) : exp (c %:S) = (c == 0)%:R %:S :> {trpoly R n}.
Proof.
case (boolP (c %:S \in @coef0_eq0 R n)) => [| p0N0].
- rewrite coef0_eq0E coef_trpolyC /= => /eqP ->.
  by rewrite eq_refl trpolyC0 trpolyC1 exp0.
- rewrite exp_coef0_isnt_0 //.
  move: p0N0; rewrite coef0_eq0E coef_trpolyC /= => /negbTE ->.
  by rewrite rmorph0.
Qed.

Lemma log_coef0_eq1 f : f \in coef0_eq1 ->
  log f = - \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i.
Proof. by rewrite /log => ->. Qed.

Lemma log_coef0_eq1_val f : f \in coef0_eq1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - val f) ^+i).
Proof.
rewrite /log => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]trpolyK !linearZ !linearN /= exp_trpoly_val trXn_trXn.
Qed.

Lemma log_coef0_isnt_1 f : f \notin coef0_eq1 -> log f = 0.
Proof. by rewrite /log => /negPf ->. Qed.

Lemma log1 : log (1 : {trpoly R n}) = 0.
Proof.
apply/trpolyP => j Hj; rewrite log_coef0_eq1 ?rpred1 // coef0 subrr.
rewrite coefN big_nat big1 ?coef0 ?oppr0 // => i /andP [Hi _].
by rewrite expr0n -[i == 0%N]negbK -lt0n Hi /= scaler0.
Qed.

End ExpLog.

Arguments log {R n}.
Arguments exp {R n}.

Notation "f ^^ r" := (expr_trpoly r f) : trpoly_scope.


Section CoefExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Type f : {trpoly R n}.

Lemma exp_in_coef0_eq1 f : (exp f \in coef0_eq1) = (f \in coef0_eq0).
Proof.
apply/idP/idP => [| Hf].
- apply/contraLR => /exp_coef0_isnt_0 ->.
  by rewrite coef0_eq1E coef0 eq_sym oner_eq0.
- rewrite exp_coef0_eq0 //.
  rewrite big_ord_recl /= fact0 invr1 scale1r expr0.
  rewrite addrC coef0_eq1_add01 ?rpred1 //.
  apply rpred_sum => [i _].
  by rewrite coef0_eq0Z // coef0_eq0X.
Qed.

Lemma coef0_exp f : f \in coef0_eq0 -> (exp f)`_0 = 1.
Proof. by rewrite -exp_in_coef0_eq1 coef0_eq1E => /eqP. Qed.

Lemma exp_unit f : f \in coef0_eq0 -> exp f \is a GRing.unit.
Proof. by rewrite -exp_in_coef0_eq1; apply coef0_eq1_unit. Qed.

Lemma log_in_coef0_eq0 f : log f \in coef0_eq0.
Proof.
case (boolP (f \in coef0_eq1)) => [f0_eq1|f0_neq1]; last first.
  by rewrite log_coef0_isnt_1 // rpred0.
rewrite log_coef0_eq1 //.
rewrite rpredN big_nat rpred_sum // => [[|i]] // _.
by rewrite coef0_eq0Z // coef0_eq0X // -coef0_eq10.
Qed.

Lemma coef0_log f : (log f)`_0 = 0.
Proof. by have := log_in_coef0_eq0 f; rewrite coef0_eq0E => /eqP. Qed.

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
by rewrite -coef_deriv primK -coef_trpolyE.
Qed.

Lemma deriv_trpolyK :
  {in @coef0_eq0 R n.+1, cancel (@deriv_trpoly R _) (@prim_trpoly R _)}.
Proof.
move=> f; rewrite coef0_eq0E => /eqP f0_eq0.
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


Theorem expD : {in (@coef0_eq0 R n) &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g f0_eq0 g0_eq0 /=.
rewrite ?(exp_coef0_eq0, rpredD) //.
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
have -> : \sum_(i < n.+1) \sum_(j < n.+1)
                   (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)  =
          \sum_(i < n.+1) \sum_(j < n.+1 | i + j <= n)
                   (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j).
  apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite (bigID (fun j => i + (nat_of_ord j) <= n)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  apply: big1_seq => /= j.
  rewrite -ltnNge; move/andP => [ n_lt_addij _].
  by rewrite trpolyMX_eq0 // scaler0.
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


Lemma expN f : f \in coef0_eq0 -> exp (- f) = (exp f)^-1.
Proof.
move=> f0_eq0; apply: (@mulrI _ (exp f)); rewrite ?divrr ?exp_unit //.
by rewrite -expD ?rpredN // subrr exp0.
Qed.

Lemma expB : {in (@coef0_eq0 R n) &, {morph exp : f g / f - g >-> f / g}}.
Proof. by move=> f g hf hg; rewrite expD ?rpredN // expN. Qed.

End ExpLogMorph.


Section MoreDerivative.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

Implicit Types (f g : {trpoly R n}).

Theorem derivXn_trpoly m :
  m != 0%N ->  {in GRing.unit, forall f,
     (f ^- m)^`() = (trXns n.-1 f) ^- m.+1 * f^`()%trpoly *- m}.
Proof.
move=> Hm /= f fU; rewrite -exprVn derivX_trpoly derivV_trpoly //.
rewrite rmorphV ?leq_pred //= => _.
rewrite !exprVn rmorphX ?leq_pred //= => _.
rewrite [_/_]mulrC mulrA mulrN mulNrn -!mulrnAr.
rewrite -!exprVn -exprD -addSnnS addn1.
by case: m Hm.
Qed.

Lemma deriv_trpoly_eq0_cst f : f^`() = 0 -> {c : R | f = c %:S}.
Proof.
move: f; case: n => [f _| m f H]; exists (f`_0).
  by rewrite {1}[f]trpoly_is_cst.
apply/trpolyP => [] [|i]; rewrite coef_trpolyC // ltnS [RHS]/= => le_im.
apply: (mulIr (nat_unit i)); rewrite mul0r.
move: H => /(congr1 (fun x : {trpoly _ _ } => x`_i)).
by rewrite coef_deriv_trpoly coef0 -mulr_natr.
Qed.

Lemma deriv_trpoly_ex_eq0 f :
  f^`() = 0 -> {x : R | (trpoly f).[x] = 0} -> f = 0.
Proof.
move=> /deriv_trpoly_eq0_cst [c ->] [x].
rewrite val_trpolyC /= hornerC => ->.
by rewrite trpolyC0.
Qed.

Lemma deriv_trpoly_eq0 f : f^`() = 0 -> f`_0 = 0 -> f = 0.
Proof.
move=> /deriv_trpoly_ex_eq0 H f0_eq0; apply: H.
by exists 0; rewrite horner_coef0.
Qed.

Lemma deriv_trpoly_ex_eq f g :
  f^`() = g^`() -> {x : R | (trpoly f).[x] = (trpoly g).[x]} -> f = g.
Proof.
move=> H [x Hx].
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_trpoly_ex_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

Lemma deriv_trpoly_eq f g : f^`() = g^`() -> f`_0 = g`_0 -> f = g.
Proof.
move=> /deriv_trpoly_ex_eq H Heq0; apply: H.
by exists 0; rewrite !horner_coef0.
Qed.

End MoreDerivative.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {trpoly R n}).


Theorem deriv_exp f : (exp f)^`() = f^`()%trpoly * (trXns n.-1 (exp f)).
Proof.
move: f; case: n => /= [| m] f.
  by rewrite [f]trpoly_is_cst deriv_trpolyC mul0r expC deriv_trpolyC.
case: (boolP (f \in coef0_eq0)) => [p0_eq0 | p0_neq0]; last first.
  by rewrite exp_coef0_isnt_0 // deriv_trpoly0 rmorph0 // mulr0.
rewrite !exp_coef0_eq0 //.
rewrite raddf_sum /= -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= rmorphD linearZ /=.
rewrite rmorphX trpolyX_eq0 ?coef0_eq0_trXns // scaler0 addr0.
rewrite rmorph_sum mulr_sumr /=.
rewrite -(big_mkord predT (fun i => (i`!%:R^-1 *: f ^+ i)^`())) /=.
rewrite big_nat_recl // expr0 linearZ /= deriv_trpoly1 scaler0 add0r.
apply: eq_bigr => i _.
rewrite !linearZ -scalerCA /= derivX_trpoly.
rewrite -scaler_nat scalerA /= rmorphX /= -scalerAl [f^`()%trpoly * _]mulrC.
congr (_ *: _).
rewrite factS natrM /= invrM ?fact_unit //.
by rewrite -mulrA [X in _ * X]mulrC divrr // mulr1.
Qed.

Theorem deriv_log f :
  f \in coef0_eq1 -> (log f)^`() = f^`()%trpoly / (trXns n.-1 f).
Proof.
case: n f => [|m] f.
  rewrite [f]trpoly_is_cst coef0_eq1E coef_trpolyC => /eqP ->.
  by rewrite !deriv_trpoly0p mul0r.
move => f0_eq1.
rewrite log_coef0_eq1 //.
rewrite !raddf_sum /= big_nat.
rewrite (eq_bigr (fun i => f^`()%trpoly * ((1 - (trXns m f)) ^+ i.-1))) =>
                                                  [|i /andP [hi _]]; last first.
- rewrite linearN linearZ /= derivX_trpoly /=.
  rewrite -scaler_nat scalerA mulrC divrr; last by case: i hi.
  rewrite scale1r !linearD /= deriv_trpoly1 add0r !linearN /=.
  by rewrite mulrN opprK trXns1 mulrC.
- rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : trXns m f \is a GRing.unit.
    by rewrite trXn_unitE -unit_trpolyE coef0_eq1_unit.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  rewrite trpolyX_eq0 ?subr0 //.
  by rewrite -coef0_eq10 coef0_eq1_trXns.
Qed.

Lemma expK : {in coef0_eq0, cancel (@exp R n) (@log R n)}.
Proof.
move => f f0_eq0 /=.
apply/eqP; rewrite -(subr_eq0 _ f); apply/eqP.
apply: (deriv_trpoly_eq0 nat_unit).
- rewrite linearB /= deriv_log ?exp_in_coef0_eq1 //.
  rewrite deriv_exp // -mulrA divrr ?mulr1 ?subrr // trXn_unitE.
  by rewrite coef0_exp // unitr1.
- by rewrite coefB coef0_log (eqP f0_eq0) subrr.
Qed.

Lemma exp_inj : {in coef0_eq0 &, injective (@exp R n)}.
Proof. exact: (can_in_inj expK). Qed.

Lemma log_inj : {in coef0_eq1 &, injective (@log R n)}.
Proof.
move=> f g f0_eq0 g0_eq0 /= Hlog.
have {Hlog} : (f / g)^`() = 0.
  rewrite deriv_div_trpoly; last exact: coef0_eq1_unit.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  apply/eqP; rewrite subr_eq0 [X in _ == X]mulrC.
  rewrite -eq_divr ?trXns_unitE -?unit_trpolyE ?coef0_eq1_unit //.
  by move/(congr1 (@deriv_trpoly R n)): Hlog; rewrite !deriv_log // => ->.
move/(deriv_trpoly_eq0_cst nat_unit) => [c Hpq].
suff Hc : c = 1 by subst c; move: Hpq; rewrite trpolyC1; apply: divr1_eq.
move/(congr1 (fun x => x * g)): Hpq.
rewrite mulrAC -mulrA divrr ?trXns_unitE -?unit_trpolyE ?coef0_eq1_unit //.
rewrite mulr1 -alg_trpolyC mulr_algl=> /(congr1 (fun x : {trpoly R n} => x`_0)).
rewrite coefZ.
move: f0_eq0 g0_eq0; rewrite !coef0_eq1E => /eqP -> /eqP ->.
by rewrite mulr1 => ->.
Qed.

Lemma logK : {in coef0_eq1 , cancel (@log R n) (@exp R n)}.
Proof.
move=> f f0_eq1 /=.
apply: log_inj => //; first by rewrite exp_in_coef0_eq1 log_in_coef0_eq0.
by rewrite expK // log_in_coef0_eq0.
Qed.

Lemma logM : {in (@coef0_eq1 R n) &, {morph log : f g / f * g >-> f + g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
apply exp_inj; rewrite ?rpredD ?log_in_coef0_eq0 //.
rewrite expD ?log_in_coef0_eq0 //.
by rewrite !logK // rpredM.
Qed.

Lemma logV : {in (@coef0_eq1 R n), {morph log : f / f^-1 >-> - f}}.
Proof.
move=> f f0_eq1 /=.
apply exp_inj; rewrite ?rpredN ?log_in_coef0_eq0 //.
rewrite expN ?log_in_coef0_eq0 //.
by rewrite !logK // rpredV.
Qed.

Lemma log_div : {in (@coef0_eq1 R n) &, {morph log : f g / f / g >-> f - g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
by rewrite logM ?rpredV // logV.
Qed.


Section ExprTrpoly.

Variable f : {trpoly R n}.
Hypothesis f0_eq1 : f \in coef0_eq1.

Let log_coef0_eq0Z c : c *: log f \in coef0_eq0.
Proof. by rewrite coef0_eq0Z // log_in_coef0_eq0. Qed.

Lemma coef0_eq1_expr c : f ^^ c \in coef0_eq1.
Proof. by rewrite /expr_trpoly exp_in_coef0_eq1 log_coef0_eq0Z. Qed.

Lemma expr_trpolyn m : f ^^ m%:R = f ^+ m.
Proof.
rewrite /expr_trpoly; elim: m => [|m IHm]; first by rewrite expr0 scale0r exp0.
rewrite -{1}add1n natrD scalerDl scale1r expD ?log_in_coef0_eq0 //.
by rewrite {}IHm logK // exprS.
Qed.

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
  (f ^^ a)^`() = a *: trXns n.-1 (f ^^ (a - 1)) * f^`()%trpoly.
Proof.
rewrite {1}/expr_trpoly deriv_exp -/(f ^^ a).
rewrite linearZ /= deriv_log // -!scalerAl; congr (_ *: _).
rewrite -mulrA mulrC; congr (_ * _).
rewrite -trXnsV ?leq_pred // -rmorphM ?leq_pred //= => _.
by rewrite mulrC expr_trpolyB expr_trpoly1.
Qed.

End ExprTrpoly.

Lemma expr_trpolyNn f m : f \in coef0_eq1 -> f ^^ (-m%:R) = f ^- m.
Proof.
move=> Hf.
by rewrite -mulN1r expr_trpolyM expr_trpolyN1 ?expr_trpolyn ?exprVn ?rpredV.
Qed.

Lemma expr_trpolyK a : a \is a GRing.unit ->
  {in coef0_eq1, cancel (@expr_trpoly R n a) (@expr_trpoly R n a^-1)}.
Proof. by move=> aU f f0_eq1; rewrite -expr_trpolyM divrr ?expr_trpoly1. Qed.

Lemma expr_trpoly_inj a : a \is a GRing.unit ->
  {in coef0_eq1 &, injective (@expr_trpoly R n a)}.
Proof. by move=> /expr_trpolyK/can_in_inj. Qed.


Local Notation "\sqrt f" := (f ^^ (2%:R^-1)).

Lemma sqrrK f :
  f \in coef0_eq1 -> \sqrt (f ^+ 2) = f :> {trpoly R n}.
Proof.
by move => Hh; rewrite -expr_trpolyn -?expr_trpolyM ?divrr ?expr_trpoly1.
Qed.

Lemma sqrtK f :
  f \in coef0_eq1 -> (\sqrt f) ^+ 2 = f :> {trpoly R n}.
Proof.
move => Hh; rewrite -expr_trpolyn ?coef0_eq1_expr //.
by rewrite -?expr_trpolyM // mulrC divrr ?expr_trpoly1.
Qed.

End DerivExpLog.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : trpoly_scope.


Section CoefExpX.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma coef1cX p c : 1 + c *: \Xo(p) \in @coef0_eq1 R p.
Proof.
by rewrite coef0_eq1E coefD coef1 coefZ coef_trXn coefX mulr0 addr0.
Qed.

Lemma deriv1cX p c : (1 + c *: \Xo(p.+1))^`() = c%:S :> {trpoly R p}.
Proof.
rewrite linearD /= deriv_trpoly1 add0r linearZ /=.
rewrite -alg_trpolyC; congr (_ *: _); apply trpoly_inj.
by rewrite (val_deriv_trpoly \Xo(p.+1)) val_trpolyX scale1r derivX.
Qed.

Theorem coef_expr1cX c a m p : m <= p ->
  ((1 + c *: \Xo(p)) ^^ a)`_m = c ^+ m * \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
elim: m p a => [|m IHm] p a lt_mp.
  rewrite big_ord0 /expr_trpoly coef0_exp ?coef0_eq0Z ?log_in_coef0_eq0 //.
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


Lemma sqrtE f g : f \in coef0_eq1 -> g ^+ 2 = f ->
  g = \sqrt f  \/  g = - \sqrt f.
Proof.
move=> /eqP f0_eq1 Heq.
have /eqP := (congr1 (fun f : {trpoly R n} => f`_0) Heq).
rewrite -subr_eq0 {}f0_eq1 expr2 coef0_trpolyM -expr2 subr_sqr_1.
rewrite mulf_eq0 => /orP [].
- by rewrite subr_eq0 -coef0_eq1E -{}Heq {f} => Hg0; left; rewrite sqrrK.
- rewrite addr_eq0 -eqr_oppLR -coefN -raddfN -coef0_eq1E -{}Heq {f} => Hg0.
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
Definition expr_trpolyn         := TruncPolyUnitRing.expr_trpolyn         nuf.
Definition expr_trpoly0         := TruncPolyUnitRing.expr_trpoly0         nuf.
Definition expr_trpoly1         := TruncPolyUnitRing.expr_trpoly1         nuf.
Definition expr_trpolyN         := TruncPolyUnitRing.expr_trpolyN         nuf.
Definition expr_trpolyD         := TruncPolyUnitRing.expr_trpolyD         nuf.
Definition expr_trpolyB         := TruncPolyUnitRing.expr_trpolyB         nuf.
Definition expr_trpolyM         := TruncPolyUnitRing.expr_trpolyM         nuf.

End TruncPolyField.

End TruncPolyField.

Export TruncPolyField.
