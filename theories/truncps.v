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

Declare Scope tfps_scope.
Delimit Scope tfps_scope with tfps.

Reserved Notation "{ 'tfps' R n }"
         (at level 0, R, n at level 2, format "{ 'tfps'  R  n }").
Reserved Notation "[ 'tfps' s <= n => F ]"
  (at level 0, n at next level, s ident, format "[ 'tfps' s <= n  =>  F ]").
Reserved Notation "[ 'tfps' s => F ]"
  (at level 0, s ident, format "[ 'tfps'  s  =>  F ]").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "\X" (at level 0).
Reserved Notation "\Xo( n )" (at level 0).
Reserved Notation "f *h g" (at level 2).
Reserved Notation "x ^^ n" (at level 29, left associativity).
Reserved Notation "f \So g" (at level 50).
Reserved Notation "\sqrt f" (at level 10).


Section SSRCompl.

Variable R : ringType.
Implicit Type (x y z : R).

Lemma expr_prod i x : x ^+ i = \prod_(j < i) x.
Proof.
elim: i => [|i IHi]; first by rewrite expr0 big_ord0.
by rewrite big_ord_recl -IHi exprS.
Qed.

Lemma commrB x y z : GRing.comm x y -> GRing.comm x z -> GRing.comm x (y - z).
Proof. by move=> com_xy com_xz; apply commrD => //; apply commrN. Qed.

Lemma commr_sum (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> GRing.comm x (F i)) -> GRing.comm x (\sum_(i <- s | P i) F i).
Proof.
move=> H; rewrite /GRing.comm mulr_suml mulr_sumr.
by apply eq_bigr => i /H.
Qed.

End SSRCompl.

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


Section TruncFPSDef.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}).

Record truncfps := MkTfps { tfps : {poly R}; _ : size tfps <= n.+1 }.

Canonical truncfps_subType :=
  Eval hnf in [subType for tfps].
Definition truncfps_eqMixin :=
  Eval hnf in [eqMixin of truncfps by <:].
Canonical truncfps_eqType :=
  Eval hnf in EqType truncfps truncfps_eqMixin.
Definition truncfps_choiceMixin :=
  [choiceMixin of truncfps by <:].
Canonical truncfps_choiceType :=
  Eval hnf in ChoiceType truncfps truncfps_choiceMixin.

Lemma tfps_inj : injective tfps. Proof. exact: val_inj. Qed.

Definition tfps_of of phant R := truncfps.
Identity Coercion type_tfps_of : tfps_of >-> truncfps.

Fact poly_of_tfps_key : unit. Proof. by []. Qed.
Definition poly_of_tfps : tfps_of (Phant R) -> {poly R} :=
  locked_with poly_of_tfps_key tfps.
Canonical poly_of_tfps_unlockable := [unlockable fun poly_of_tfps].

Lemma tfpsE : tfps =1 poly_of_tfps.
Proof. by case=> p Hp; rewrite unlock. Qed.

Coercion seq_of_tfps (f : truncfps) : seq R := @tfps f.

Lemma size_tfps (f : tfps_of (Phant R)) : size f <= n.+1.
Proof. by case: f. Qed.

Definition coeftfps_head h i (p : tfps_of (Phant R)) := let: tt := h in p`_i.

End TruncFPSDef.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope ring_scope with tfps_of.
Bind Scope ring_scope with truncfps.
Arguments tfps {R n%N}.
Arguments tfps_inj {R} [p1%R p2%R] : rename.
Notation "{ 'tfps' R n }" :=  (tfps_of n (Phant R)).
Arguments coeftfps_head {R n} h i%N p%R.
Notation coeftfps i := (coeftfps_head tt i).

Hint Resolve size_tfps : core.


Section CoefTFPS.

Variable R : ringType.
Variable n : nat.

Implicit Types (p q r s : {poly R}) (f g : {tfps R n}).

Lemma size_tfpsE f : size f = size (tfps f).
Proof. by []. Qed.

Lemma coef_tfpsE f i : f`_i = (tfps f)`_i.
Proof. by []. Qed.

Lemma coef_tfps f i : f`_i = if i <= n then f`_i else 0.
Proof.
case: (leqP i n) => Hi //.
by rewrite nth_default // (leq_trans (size_tfps _) Hi).
Qed.

Lemma tfpsP f g : (forall i, i <= n -> f`_i = g`_i) <-> (f = g).
Proof.
split => [H | H i Hi].
- apply/tfps_inj/polyP => i; rewrite [LHS]coef_tfps [RHS]coef_tfps.
  by case: leqP => //; apply: H.
- move: H => /(congr1 tfps)/(congr1 (fun r => r`_i)).
  by rewrite coef_tfps Hi.
Qed.


Definition Tfps_of (p : {poly R}) (p_small : size p <= n.+1)
  : {tfps R n} := MkTfps p_small.

Fact trXn_subproof p : size (Poly (take n.+1 p)) <= n.+1.
Proof. by apply: (leq_trans (size_Poly _)); rewrite size_take geq_minl. Qed.
Definition trXn_def p := Tfps_of (trXn_subproof p).
Fact trXn_key : unit. Proof. by []. Qed.
Definition trXn := locked_with trXn_key trXn_def.
Canonical trXn_unlockable := [unlockable fun trXn].

Definition tfpsC_def c := trXn (c %:P).
Fact tfpsC_key : unit. Proof. by []. Qed.
Definition tfpsC := locked_with tfpsC_key tfpsC_def.
Canonical tfpsC_unlockable := [unlockable fun tfpsC].

Definition tfps_of_fun (f : nat -> R) := Tfps_of (size_poly _ f).

Lemma trXnE p : tfps (trXn p) = Poly (take n.+1 p) :> {poly R}.
Proof. by rewrite unlock. Qed.

Lemma coef_trXn p i : (trXn p)`_i = if i <= n then p`_i else 0.
Proof.
rewrite coef_tfpsE trXnE coef_Poly.
case: leqP => Hi; first by rewrite nth_take.
by rewrite nth_default // size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

Lemma trXnP p q : (forall i, i <= n -> p`_i = q`_i) <-> (trXn p = trXn q).
Proof.
rewrite -tfpsP; split => H i Hi.
- by rewrite !coef_trXn Hi; apply H.
- by have := H i Hi; rewrite !coef_trXn Hi.
Qed.

Lemma tfpsK : cancel (@tfps R n) trXn.
Proof. by move=> f; apply/tfpsP => i Hi; rewrite coef_trXn Hi. Qed.

Lemma trXnK p : size p <= n.+1 -> tfps (trXn p) = p.
Proof.
move=> le_szn; apply polyP => i.
rewrite -coef_tfpsE coef_trXn; case: leqP => // /(leq_trans le_szn) leq_szi.
by rewrite nth_default.
Qed.

Lemma coef0_trXn (p : {poly R}) : (trXn p)`_0 = p`_0.
Proof. by rewrite coef_trXn leq0n. Qed.


Lemma tfpsCE c : tfpsC c = trXn c%:P.
Proof. by rewrite unlock. Qed.

Lemma coef_tfpsC c i : (tfpsC c)`_i = if i == 0%N then c else 0.
Proof.
by rewrite tfpsCE coef_trXn coefC; case: i => //= i; rewrite if_same.
Qed.

Lemma val_tfpsC (c : R) : tfps (tfpsC c) = c %:P.
Proof. by apply/polyP => i /=; rewrite coef_tfpsC coefC. Qed.

Lemma tfpsCK : cancel tfpsC (coeftfps 0).
Proof. by move=> c; rewrite [coeftfps 0 _]coef_tfpsC. Qed.


Lemma tfpsC_inj : injective tfpsC.
Proof.
by move=> c1 c2 eqc12; have:= coef_tfpsC c2 0; rewrite -eqc12 coef_tfpsC.
Qed.


Lemma coef_tfps_of_fun (f : nat -> R) i :
  (tfps_of_fun f)`_i = if i <= n then f i else 0.
Proof. by rewrite /tfps_of_fun coef_poly ltnS. Qed.


Definition poly_trXn_class := QuotClass tfpsK.
Canonical poly_trXn_type := QuotType {tfps R n} poly_trXn_class.

Lemma poly_trXn_quotP p q :
  reflect
    (forall i, (i <= n)%N -> p`_i = q`_i)
    (p == q %[mod {tfps R n}])%qT.
Proof. by rewrite !unlock /pi_phant; apply (iffP eqP); rewrite trXnP. Qed.

End CoefTFPS.

Local Open Scope tfps_scope.

Notation "[ 'tfps' s <= n => F ]" :=
  (tfps_of_fun n (fun s => F)) : tfps_scope.
Notation "[ 'tfps' s => F ]" := [tfps s <= _ => F] : tfps_scope.
Notation "c %:S" := (tfpsC _ c) (at level 2) : tfps_scope.
Notation "\X" := (trXn _ 'X) : tfps_scope.
Notation "\Xo( n )" := (trXn n 'X) (only parsing): tfps_scope.


Section TFPSTheory.

Variable (R : ringType).
Implicit Types (p q r s : {poly R}).

Fact trXnC n a : tfps (trXn n a%:P) = a%:P :> {poly R}.
Proof.
apply/polyP => i; rewrite coef_trXn coefC.
by case: eqP => [->|_] //; rewrite if_same.
Qed.

Fact trXn_trXn p m n : m <= n -> trXn m (tfps (trXn n p)) = trXn m p.
Proof.
move=> le_mn; apply/trXnP => i le_im.
by rewrite coef_trXn (leq_trans le_im le_mn).
Qed.

Variable (n : nat).

Lemma trXnCE m a : trXn n (tfps (a%:S : {tfps R m})) = a%:S.
Proof. by apply tfps_inj; rewrite val_tfpsC !tfpsCE. Qed.

Lemma trXn_mull p q : trXn n (tfps (trXn n p) * q) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans le_ji le_in).
Qed.

Lemma trXn_mulr p q : trXn n (p * tfps (trXn n q)) = trXn n (p * q).
Proof.
apply/trXnP => i le_in /=; rewrite !coefM.
apply eq_bigr => [] [j] /=; rewrite ltnS => le_ji _.
by rewrite coef_trXn (leq_trans (leq_subr _ _) le_in).
Qed.

Lemma trXn_mul p q :
  trXn n (tfps (trXn n p) * tfps (trXn n q)) = trXn n (p * q).
Proof. by rewrite trXn_mulr trXn_mull. Qed.


(* zmodType structure *)
Implicit Types (f g : {tfps R n}).

Fact zero_tfps_subproof : size (0 : {poly R}) <= n.+1.
Proof. by rewrite size_poly0. Qed.
Definition zero_tfps := Tfps_of zero_tfps_subproof.

Lemma add_tfps_subproof f g :
  size (tfps f + tfps g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_tfps. Qed.
Definition add_tfps f g := Tfps_of (add_tfps_subproof f g).

Lemma opp_tfps_subproof f : size (- tfps f) <= n.+1.
Proof. by rewrite size_opp ?size_tfps. Qed.
Definition opp_tfps f := Tfps_of (opp_tfps_subproof f).

Program Definition tfps_zmodMixin :=
  @ZmodMixin {tfps R n} zero_tfps opp_tfps add_tfps _ _ _ _.
Next Obligation. by move => f1 f2 f3; apply/tfps_inj/addrA. Qed.
Next Obligation. by move => f1 f2; apply/tfps_inj/addrC. Qed.
Next Obligation. by move => f; apply/tfps_inj/add0r. Qed.
Next Obligation. by move => f; apply/tfps_inj/addNr. Qed.
Canonical tfps_zmodType := ZmodType {tfps R n} tfps_zmodMixin.

Fact trXn_is_additive : additive (trXn n).
Proof.
by move=> f g; apply/tfpsP => i Hi; rewrite coefB !coef_trXn coefB Hi.
Qed.
Canonical trXn_additive := Additive trXn_is_additive.

Lemma coef_tfps0 i : (0 : {tfps R n})`_i = 0.
Proof. by rewrite coef0. Qed.

Lemma trXn0 : trXn n 0 = 0.
Proof. exact: raddf0. Qed.

Fact tfps_is_additive : additive (@tfps R n : {tfps R n} -> {poly R}).
Proof. by []. Qed.
Canonical tfps_additive := Additive tfps_is_additive.

Lemma tfpsC_is_additive : additive (@tfpsC R n : R -> {tfps R n}).
Proof.
move=> c1 c2; apply tfps_inj.
by rewrite !val_tfpsC !raddfB /= !val_tfpsC.
Qed.
Canonical tfpsC_additive := Additive tfpsC_is_additive.

Lemma tfpsC0 : (0%:S : {tfps R n}) = 0.
Proof. exact: raddf0. Qed.


(* ringType structure *)
Fact one_tfps_proof : size (1 : {poly R}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.
Definition one_tfps : {tfps R n} := Tfps_of one_tfps_proof.

Definition mul_tfps f g := trXn n (tfps f * tfps g).
Definition hmul_tfps f g := [tfps j <= n => f`_j * g`_j].
Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsA : associative hmul_tfps.
Proof.
by move=> f1 f2 f3; apply/tfpsP => i Hi; rewrite !coef_poly ltnS Hi mulrA.
Qed.

Lemma hmul_tfps0r f : 0 *h f = 0.
Proof. by apply/tfpsP => i Hi; rewrite coef_poly coef0 mul0r if_same. Qed.

Lemma hmul_tfpsr0 f : f *h 0 = 0.
Proof. by apply/tfpsP => i Hi; rewrite coef_poly coef0 mulr0 if_same. Qed.

Program Definition tfps_ringMixin :=
  @RingMixin [zmodType of {tfps R n}] one_tfps mul_tfps _ _ _ _ _ _.
Next Obligation. move=> f1 f2 f3;
                 by rewrite /mul_tfps trXn_mulr trXn_mull mulrA. Qed.
Next Obligation. by move=> p; rewrite /mul_tfps mul1r tfpsK. Qed.
Next Obligation. by move=> p; rewrite /mul_tfps mulr1 tfpsK. Qed.
Next Obligation. by move=> f1 f2 f3; rewrite /mul_tfps mulrDl raddfD. Qed.
Next Obligation. by move=> f1 f2 f3; rewrite /mul_tfps mulrDr raddfD. Qed.
Next Obligation. by rewrite -val_eqE oner_neq0. Qed.
Canonical tfps_ringType := RingType {tfps R n} tfps_ringMixin.


Lemma coef_tfps1 i : (1 : {tfps R n})`_i = (i == 0%N)%:R.
Proof. by rewrite coef1. Qed.

Lemma trXn1 : trXn n 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_trXn Hi. Qed.

Fact trXn_is_multiplicative : multiplicative (@trXn R n).
Proof. by split => [f g|] /=; [rewrite -trXn_mul | rewrite trXn1]. Qed.
Canonical trXn_multiplicative := AddRMorphism trXn_is_multiplicative.

Lemma mul_tfps_val f g : f * g = trXn n (tfps f * tfps g).
Proof. by []. Qed.

Lemma coefM_tfps f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_j * g`_(i - j) else 0.
Proof. by rewrite !coef_tfpsE mul_tfps_val coef_trXn coefM. Qed.

Lemma coefMr_tfps f g (i : nat) :
  (f * g)`_i = if i <= n then \sum_(j < i.+1) f`_(i - j) * g`_j else 0.
Proof. by rewrite !coef_tfpsE mul_tfps_val coef_trXn coefMr. Qed.

Lemma exp_tfps_val f (m : nat) : f ^+ m = trXn n ((tfps f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphX /= tfpsK -exprS.
Qed.

Lemma tfpsC_is_multiplicative :
  multiplicative (@tfpsC R n : R -> {tfps R n}).
Proof.
split => [c1 c2|]; last by rewrite tfpsCE trXn1.
apply tfps_inj; rewrite mul_tfps_val !val_tfpsC -rmorphM /=.
apply/polyP => i; rewrite coef_tfps coef_trXn coefC; case: i => //= i.
by rewrite !if_same.
Qed.
Canonical tfpsC_rmorphism := AddRMorphism tfpsC_is_multiplicative.

Lemma tfpsC1 : (1%:S : {tfps R n}) = 1.
Proof. exact: rmorph1. Qed.

Lemma tfpsCM :
  {morph (fun x => (x%:S : {tfps R n})) : a b / a * b >-> a * b}.
Proof. exact: rmorphM. Qed.


(* lmodType structure *)
Lemma scale_tfps_subproof (c : R) f : size (c *: val f) <= n.+1.
Proof. exact: leq_trans (size_scale_leq _ _) (size_tfps _). Qed.
Definition scale_tfps (c : R) f := Tfps_of (scale_tfps_subproof c f).

Program Definition tfps_lmodMixin :=
  @LmodMixin R [zmodType of {tfps R n}] scale_tfps _ _ _ _.
Next Obligation. by apply/tfpsP => i le_in /=; rewrite !coefZ mulrA. Qed.
Next Obligation.
  by move=> x; apply/tfpsP => i le_in; rewrite coef_tfpsE /= scale1r. Qed.
Next Obligation.
  by move=> r x y; apply/tfpsP => i; rewrite coef_tfpsE /= scalerDr. Qed.
Next Obligation.
  by move=> r s; apply/tfpsP => i; rewrite coef_tfpsE /= scalerDl. Qed.
Canonical tfps_lmodType :=
  Eval hnf in LmodType R {tfps R n} tfps_lmodMixin.

Fact trXn_is_linear : linear (@trXn R n).
Proof.
move=> c f g; apply/tfpsP => i Hi.
by rewrite !(coefD, coefZ, coef_trXn) Hi.
Qed.
Canonical trXn_linear := AddLinear trXn_is_linear.

Fact tfps_is_linear : linear (@tfps R n : {tfps R n} -> {poly R}).
Proof. by []. Qed.
Canonical tfps_linear := AddLinear tfps_is_linear.


(* lalgType structure *)
Fact scale_tfpsAl c f g : scale_tfps c (f * g) = (scale_tfps c f) * g.
Proof.
by apply tfps_inj; rewrite /= -linearZ  /= !mul_tfps_val -scalerAl linearZ.
Qed.
Canonical tfps_lalgType :=
  Eval hnf in LalgType R {tfps R n} scale_tfpsAl.
Canonical trXn_lrmorphism := AddLRMorphism trXn_is_linear.


Lemma alg_tfpsC (c : R) : c%:A = c%:S.
Proof. by apply/tfps_inj; rewrite {1}val_tfpsC -alg_polyC. Qed.

(* Test *)
Example trXn_poly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Example trXn_poly1 : trXn n (1 : {poly R}) = 1.
Proof. by rewrite rmorph1. Qed.

Lemma trXnZ (c : R) (p : {poly R}) : trXn n (c *: p) =  c *: (trXn n p).
Proof. by rewrite linearZ. Qed.


Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsr1 f : f *h 1 = (f`_0)%:S.
Proof.
apply/tfpsP => i.
rewrite coef_tfpsC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_tfps1r f : 1 *h f = (f`_0)%:S.
Proof.
apply/tfpsP => i.
rewrite coef_tfpsC coef_poly ltnS coef1 => ->.
by case: i => [|i]; rewrite ?mul1r ?mul0r.
Qed.

Lemma tfps_is_cst (g : {tfps R 0}) : g = (g`_0) %:S.
Proof.
apply/tfps_inj; rewrite val_tfpsC.
by apply: size1_polyC; rewrite size_tfps.
Qed.


Lemma coeftfpsE f i : coeftfps i f = coefp i (tfps f).
Proof. by rewrite /= coef_tfpsE. Qed.

Fact coeftfps_is_additive i :
  additive (coeftfps i : {tfps R n} -> R).
Proof. by move=> f g; exact: coefB. Qed.
Canonical coeftfps_additive i := Additive (coeftfps_is_additive i).
Lemma coeftD f g i : (f + g)`_i = f`_i + g`_i.
Proof. exact: (raddfD (coeftfps_additive i)). Qed.
Lemma coeftN f i : (- f)`_i = - f`_i.
Proof. exact: (raddfN (coeftfps_additive i)). Qed.
Lemma coeftB f g i : (f - g)`_i = f`_i - g`_i.
Proof. exact: (raddfB (coeftfps_additive i)). Qed.
Lemma coeftMn f k i : (f *+ k)`_i = f`_i *+ k.
Proof. exact: (raddfMn (coeftfps_additive i)). Qed.
Lemma coeftMNn f k i : (f *- k)`_i = f`_i *- k.
Proof. exact: (raddfMNn (coeftfps_additive i)). Qed.
Lemma coeft_sum I (r : seq I) (P : pred I) (F : I -> {tfps R n}) k :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. exact: (raddf_sum (coeftfps_additive k)). Qed.

Fact coeftfps_is_linear i :
  scalable_for *%R (coeftfps i : {tfps R n} -> R).
Proof. by move=> c g; rewrite /= !coef_tfpsE !linearZ coefZ. Qed.
Canonical coeftfps_linear i := AddLinear (coeftfps_is_linear i).

Lemma coeftZ a f i : (a *: f)`_i = a * f`_i.
Proof. exact: (scalarZ [linear of (coeftfps i)]). Qed.


Fact coeftfps0_is_multiplicative :
  multiplicative (coeftfps 0 : {tfps R n} -> R).
Proof.
split=> [p q|]; rewrite !coeftfpsE; last by rewrite polyCK.
rewrite mul_tfps_val /= -!/(_`_0) coef_trXn /= -!/(_`_0) -!/(coefp 0 _).
by rewrite rmorphM.
Qed.
Canonical coeftfps0_rmorphism := AddRMorphism coeftfps0_is_multiplicative.
Canonical coeftfps0_lrmorphism := [lrmorphism of coeftfps 0].

Fact coef0_tfpsM f g : (f * g)`_0 = f`_0 * g`_0.
Proof. exact: (rmorphM coeftfps0_rmorphism). Qed.
Fact coef0_tfpsX f i : (f ^+ i)`_0 = f`_0 ^+ i.
Proof. exact: (rmorphX coeftfps0_rmorphism). Qed.

End TFPSTheory.


Section TrXnT.

Variable R : ringType.

Definition trXnt m n : {tfps R m} -> {tfps R n} :=
  @trXn R n \o (@tfps R m).

Variables (m n p : nat).
Implicit Type (f : {tfps R m}).

Lemma coef_trXnt f i : (trXnt n f)`_i = if i <= n then f`_i else 0.
Proof. by rewrite coef_trXn -coef_tfpsE. Qed.

Lemma trXntE f : trXnt n f = trXn n (tfps f).
Proof. by []. Qed.

Lemma trXnt_id f : trXnt m f = f.
Proof. by rewrite /trXnt /= tfpsK. Qed.

Fact trXnt_trXnt f :
  p <= n -> trXnt p (trXnt n f) = trXnt p f.
Proof. exact: trXn_trXn. Qed.

Lemma trXntC a : trXnt n (a%:S : {tfps R m}) = a%:S.
Proof. exact: trXnCE. Qed.

Lemma trXnt0 : @trXnt m n 0 = 0.
Proof. exact: trXn0. Qed.
Lemma trXnt1 : @trXnt m n 1 = 1.
Proof. exact: trXn1. Qed.

Fact trXnt_is_linear : linear (@trXnt m n).
Proof. by move=> c f g; rewrite !trXntE !linearP. Qed.
Canonical trXnt_additive := Additive trXnt_is_linear.
Canonical trXnt_linear := AddLinear trXnt_is_linear.

Hypothesis H : n <= m.
Fact trXnt_is_multiplicative : multiplicative (@trXnt m n).
Proof.
split=> [f g|] /=; last exact trXnt1.
rewrite /trXnt /= mul_tfps_val /=.
by rewrite -rmorphM /= trXn_trXn.
Qed.
Canonical trXnt_multiplicative := AddRMorphism trXnt_is_multiplicative.
Canonical trXnt_lrmorphism := AddLRMorphism trXnt_is_linear.

End TrXnT.


Section TestTrXnT.

Variable R : ringType.
Variables (m n p : nat).
Implicit Type (f g : {tfps R m}).

(* Test *)
Example trXnt_tfps0 : trXnt n (0 : {tfps R m}) = 0.
Proof. by rewrite linear0. Qed.

Example trXn_tfps1 : trXn n (tfps (1 : {tfps R m})) = 1.
Proof. by rewrite rmorph1. Qed.

Example trXntZ c f : trXnt n (c *: f) =  c *: (trXnt n f).
Proof. by rewrite linearZ. Qed.

Example trXntM f g : n <= m -> trXnt n (f * g) = trXnt n f * trXnt n g.
Proof. by move=> H; rewrite rmorphM. Qed.

Example trXntM12 (f g : {tfps R 2}) :
  trXnt 1 (f * g) =  (trXnt 1 f) * (trXnt 1 g).
Proof. by rewrite rmorphM. Qed.

End TestTrXnT.


Section TFPSX.

Variable (R : ringType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma tfps0X m : m = 0%N -> \Xo(m) = 0 :> {tfps R m}.
Proof.
by move=> ->; rewrite (tfps_is_cst \X) coef_trXn coefX /= tfpsC0.
Qed.

Lemma val_tfpsSX m : tfps (\Xo(m.+1)) = 'X%R :> {poly R}.
Proof.
apply/polyP => i.
by rewrite coef_trXn coefX; case: eqP => [->|] // _; rewrite if_same.
Qed.

Lemma val_tfpsX m : tfps (\Xo(m)) = (m != 0%N)%:R *: 'X%R :> {poly R}.
Proof.
case: m => [|m]; first by rewrite tfps0X /= ?scale0r.
by rewrite val_tfpsSX /= scale1r.
Qed.

Lemma coef_tfpsX m i :
  (\X : {tfps R m})`_i = (m != 0%N)%:R * (i == 1%N)%:R.
Proof. by rewrite coef_tfpsE val_tfpsX coefZ coefX. Qed.

Lemma trXn_tfpsX m : @trXn R n (tfps \Xo(m.+1)) = \X.
Proof.
case: n => [|n'].
  rewrite [RHS]tfps0X //; apply tfpsP => i.
  rewrite leqn0 => /eqP ->.
  by rewrite coef_tfps0 coef_trXn -coef_tfpsE coef_tfpsX /= mulr0.
by apply tfps_inj; rewrite !val_tfpsSX.
Qed.

Lemma trXnt_tfpsX m : @trXnt R _ n \Xo(m.+1) = \X.
Proof. exact: trXn_tfpsX. Qed.

Lemma commr_tfpsX f : GRing.comm f \X.
Proof.
apply/tfpsP => i _.
by rewrite !mul_tfps_val /= trXn_mull trXn_mulr commr_polyX.
Qed.

Lemma expr_cX (c : R) i : (c *: \Xo(n)) ^+ i = (c ^+ i) *: \X ^+ i.
Proof.
rewrite -mulr_algl exprMn_comm; last exact: commr_tfpsX.
by rewrite -in_algE -rmorphX /= mulr_algl.
Qed.

Lemma coef_tfpsXM f i :
  (\X * f)`_i = if i == 0%N then 0 else if i <= n then f`_i.-1 else 0.
Proof. by rewrite !mul_tfps_val /= trXn_mull coef_trXn coefXM; case: i. Qed.

Lemma coef_tfpsXnM f k i :
  (\X ^+ k * f)`_i = if i < k then 0 else if i <= n then f`_(i - k) else 0.
Proof.
elim: k i => [|k IHk] i.
  by rewrite expr0 ltn0 mul1r subn0 {1}coef_tfps.
rewrite exprS -mulrA coef_tfpsXM {}IHk.
case: i => [|i]//=; rewrite ltnS subSS.
by case: (ltnP i n) => [/ltnW ->|]//; rewrite if_same.
Qed.

Lemma coef_tfpsXn i k :
  ((\X : {tfps R n})^+ k)`_i = ((i <= n) && (i == k%N))%:R.
Proof.
rewrite -[_ ^+ k]mulr1 coef_tfpsXnM coef1 -/(leq _ _).
case: (altP (i =P k)) => [-> | Hneq]; first by rewrite ltnn leqnn; case: leqP.
case: (leqP i n) => _; last by rewrite if_same.
case: ltnP => //=.
by rewrite [i <= k]leq_eqVlt (negbTE Hneq) ltnNge => ->.
Qed.

Lemma tfps_def f : f = \sum_(i < n.+1) f`_i *: \X ^+ i.
Proof.
apply/tfpsP => j le_jn; have:= le_jn; rewrite -ltnS => lt_jn1.
rewrite coeft_sum /= (bigD1 (Ordinal lt_jn1)) //=.
rewrite coeftZ coef_tfpsXn eqxx le_jn mulr1.
rewrite big1 ?addr0 // => [[i /= Hi]]; rewrite -val_eqE /= => Hneq.
by rewrite coeftZ coef_tfpsXn eq_sym (negbTE Hneq) andbF mulr0.
Qed.

End TFPSX.


Section TFPSConvRing.

Variable (R : ringType) (n : nat).

Fact size_convr_subproof (f : {tfps R n}) :
  size (map_poly (fun c : R => c : R^c) (tfps f)) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_tfps. Qed.
Definition convr_tfps f : {tfps R^c n} := Tfps_of (size_convr_subproof f).

Fact size_iconvr_subproof (f : {tfps R^c n}) :
  size (map_poly (fun c : R^c => c : R) (tfps f)) <= n.+1.
Proof. by rewrite size_map_inj_poly ?size_tfps. Qed.
Definition iconvr_tfps f : {tfps R n} := Tfps_of (size_iconvr_subproof f).

Fact convr_tfps_is_additive : additive convr_tfps.
Proof.
by move=> f g; apply/tfpsP => i _; rewrite /= coefB !coef_map_id0 // coefB.
Qed.
Canonical convr_tfps_additive := Additive convr_tfps_is_additive.

Fact iconvr_tfps_is_additive : additive iconvr_tfps.
Proof.
by move=> f g; apply/tfpsP => i _; rewrite /= coefB !coef_map_id0 // coefB.
Qed.
Canonical iconvr_tfps_additive := Additive iconvr_tfps_is_additive.

Lemma convr_tfpsK : cancel convr_tfps iconvr_tfps.
Proof. by move=> f; apply/tfpsP => i _; rewrite !coef_map_id0. Qed.
Lemma iconvr_tfpsK : cancel iconvr_tfps convr_tfps.
Proof. by move=> f; apply/tfpsP => i _; rewrite !coef_map_id0. Qed.

Lemma convr_tfps1 : convr_tfps 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_map_id0 // !coef1. Qed.
Lemma iconvr_tfps1 : iconvr_tfps 1 = 1.
Proof. by apply/tfpsP => i Hi; rewrite coef_map_id0 // !coef1. Qed.

Lemma convr_tfpsM f g :
  convr_tfps f * convr_tfps g = convr_tfps (g * f).
Proof.
apply/tfpsP => i Hi.
rewrite coefM_tfps coef_map_id0 // coefMr_tfps Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.
Lemma iconvr_tfpsM f g :
  iconvr_tfps f * iconvr_tfps g = iconvr_tfps (g * f).
Proof.
apply/tfpsP => i Hi.
rewrite coefM_tfps coef_map_id0 // coefMr_tfps Hi.
by apply eq_bigr => j _ /=; rewrite !coef_map_id0.
Qed.

End TFPSConvRing.


Section TFPSComRing.

Variable (R : comRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact mul_tfpsC f g : f * g = g * f.
Proof. by rewrite !mul_tfps_val mulrC. Qed.
Canonical tfps_comRingType :=
  Eval hnf in ComRingType {tfps R n} mul_tfpsC.
Canonical tfps_algType := Eval hnf in CommAlgType R {tfps R n}.

Lemma hmul_tfpsC : commutative (@hmul_tfps R n).
Proof. by move=> f1 f2; apply/tfpsP => i; rewrite !coef_poly mulrC. Qed.

End TFPSComRing.


Section TFPSUnitRingLeft.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition unit_tfps : pred {tfps R n} := fun f => f`_0 \in GRing.unit.

Fixpoint inv_tfps_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then inv_tfps_rec f b m
    else -f`_0%N^-1 * (\sum_(i < m) f`_i.+1 * (inv_tfps_rec f b (m - i.+1)%N))
  else f`_0%N^-1.
Definition inv_tfps f : {tfps R n} :=
  if unit_tfps f then [tfps i <= n => inv_tfps_rec f i i] else f.

Lemma coef0_inv_tfps f : unit_tfps f -> (inv_tfps f)`_0 = f`_0^-1.
Proof. by rewrite /inv_tfps => ->; rewrite coef_tfps_of_fun. Qed.

Lemma coefS_inv_tfps f m :
  unit_tfps f -> m < n ->
  (inv_tfps f)`_m.+1 =
  - f`_0%N^-1 *
    (\sum_(i < m.+1) f`_i.+1 * (inv_tfps f)`_(m - i)%N).
Proof.
move=> s_unit lt_mn.
rewrite /inv_tfps s_unit coef_tfps_of_fun /= ltnn lt_mn; congr (- _ * _).
apply: eq_bigr => [[i]/=]; rewrite ltnS => le_im _.
rewrite coef_tfps_of_fun (leq_trans (leq_subr _ _) (ltnW lt_mn)).
congr (_ * _); rewrite /bump /= subSS.
move: (m - i)%N (leq_subr i m) {le_im} => {}i le_im.
move: le_im => /subnKC <-; elim: (m - i)%N => [|k IHl]; first by rewrite addn0.
by rewrite addnS /= leq_addr.
Qed.

Lemma mul_tfpsVr : {in unit_tfps, right_inverse 1 inv_tfps *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/tfpsP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  by rewrite coef1 coef0_tfpsM coef0_inv_tfps ?divrr.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/=.
case: (ltnP m.+1 n.+1) => Hmn; last first.
  by rewrite nth_default ?(leq_trans (size_tfps _)).
rewrite coefM_tfps -ltnS Hmn big_ord_recl [val ord0]/= subn0.
rewrite coefS_inv_tfps // mulNr mulrN mulVKr // addrC.
apply/eqP; rewrite subr_eq0; apply/eqP.
by apply eq_bigr => [] [i] /=.
Qed.

Lemma inv_tfps0id : {in [predC unit_tfps], inv_tfps =1 id}.
Proof.
by move=> s; rewrite inE /= /inv_tfps unfold_in /unit_tfps => /negbTE ->.
Qed.

End TFPSUnitRingLeft.


Section TruncFPSUnitRing.

Variable (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition invl_tfps f := iconvr_tfps (inv_tfps (convr_tfps f)).

Lemma mul_tfpsVl : {in @unit_tfps R n, left_inverse 1 invl_tfps *%R}.
Proof.
move=> f Hf; rewrite /invl_tfps -{2}(convr_tfpsK f).
rewrite iconvr_tfpsM mul_tfpsVr ?iconvr_tfps1 //.
by move: Hf; rewrite !unfold_in coef_map_id0.
Qed.

(* General semi-group theory : left inverse = right inverse *)
Lemma invr_tfpsE f : unit_tfps f -> inv_tfps f = invl_tfps f.
Proof.
move=> H; have:= erefl (invl_tfps f * f * inv_tfps f).
by rewrite -{2}mulrA mul_tfpsVl // mul1r mul_tfpsVr // mulr1.
Qed.

Lemma mul_tfpsrV :
  {in @unit_tfps R n, left_inverse 1 (@inv_tfps R n) *%R}.
Proof. by move=> f Hs; rewrite invr_tfpsE // mul_tfpsVl. Qed.

Lemma unit_tfpsP f g : g * f = 1 /\ f * g = 1 -> unit_tfps f.
Proof.
move=> [] /(congr1 (fun x : {tfps _ _ } => x`_0)).
rewrite coef1 coef0_tfpsM => Hl.
move=>    /(congr1 (fun x : {tfps _ _ } => x`_0)).
rewrite coef1 coef0_tfpsM => Hr.
by rewrite /unit_tfps; apply/unitrP; exists g`_0.
Qed.

Definition tfps_unitMixin :=
  UnitRingMixin mul_tfpsrV (@mul_tfpsVr _ _) unit_tfpsP (@inv_tfps0id _ _).
Canonical tfps_unitRingType :=
  Eval hnf in UnitRingType {tfps R n} tfps_unitMixin.


Lemma unit_tfpsE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma trXn_unitE (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_tfpsE coef0_trXn. Qed.

Fact coef0_tfpsV f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
case (boolP (f \is a GRing.unit))=> [f_unit|]; first by rewrite coef0_inv_tfps.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite unit_tfpsE => /invr_out ->.
Qed.

Lemma coef_tfpsV f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_j.+1 * f^-1`_(i - j.+1)).
Proof.
move=> funit; case: ltnP => Hi.
  by rewrite -(tfpsK f^-1) coef_trXnt (ltn_geF Hi).
case: i Hi => [|i] Hi; first by rewrite eq_refl coef0_tfpsV.
by rewrite coefS_inv_tfps.
Qed.

Lemma tfpsCV (c : R) : (trXn n c%:P)^-1 = trXn n (c^-1)%:P.
Proof.
case (boolP (c \in GRing.unit)) => [Uc | nUc].
  by rewrite -/((trXn n \o @polyC R) _) -rmorphV.
by rewrite !invr_out // unit_tfpsE coef_trXn coefC.
Qed.

End TruncFPSUnitRing.


Section TruncFPSTheoryUnitRing.

Variable (R : unitRingType) (m n : nat).
Implicit Types (f g : {tfps R n}).

Lemma trXnt_unitE f :
  ((trXnt m f) \is a GRing.unit) = (f`_0 \is a GRing.unit).
Proof. exact: trXn_unitE. Qed.

Lemma trXntV f : m <= n -> trXnt m (f^-1) = (trXnt m f) ^-1.
Proof.
move=> leq_mn.
case (boolP (f`_0 \is a GRing.unit)) => f0U; first last.
  by rewrite !invr_out // unit_tfpsE ?coef0_trXn.
by rewrite rmorphV.
Qed.

Lemma trXnV f : m <= n -> trXn m (tfps f^-1) = (trXn m (tfps f)) ^-1.
Proof. move=> leq_mn; exact: trXntV. Qed.

End TruncFPSTheoryUnitRing.


Section TFPSComUnitRing.

Variable (R : comUnitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Canonical tfps_comUnitRingType := [comUnitRingType of {tfps R n}].
Canonical tfps_unitAlgType := Eval hnf in [unitAlgType R of {tfps R n}].

End TFPSComUnitRing.


Section TFPSIDomain.

Variable R : idomainType.

Lemma poly_modXn n (p : {poly R}) : p %% 'X^n = Poly (take n p).
Proof.
rewrite -{1}(poly_cat p n) addrC mulrC Pdiv.IdomainUnit.modp_addl_mul_small //.
- by rewrite lead_coefXn unitr1.
- rewrite size_polyXn ltnS (leq_trans (size_Poly _)) //.
  by rewrite size_take -/(minn _ _) geq_minl.
Qed.

Lemma trXn_modE m (p : {poly R}) : p %% 'X^ m.+1 = tfps (trXn m p).
Proof. by apply/val_inj => /=; rewrite trXnE poly_modXn. Qed.

Fact tfps_modp (n m : nat) (p : {poly R}) : n <= m ->
  trXn n (p %% 'X^m.+1) = trXn n p.
Proof. by move=> lt_nm; apply/val_inj; rewrite /= trXn_modE trXn_trXn. Qed.

Variable n : nat.
Implicit Types (f g : {tfps R n}).

Fact mod_tfps (m : nat) f : n <= m -> (tfps f) %% 'X^m.+1 = (tfps f).
Proof.
move=> leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_tfps _)).
Qed.

End TFPSIDomain.


Section MapTFPS.

Variables (K L : ringType) (n : nat) (f : {rmorphism K -> L}).

Implicit Type g h : {tfps K n}.

Fact map_tfps_subproof g : size (map_poly f (val g)) <= n.+1.
Proof.
by rewrite map_polyE (leq_trans (size_Poly _)) // size_map size_tfps.
Qed.
Definition map_tfps g := Tfps_of (map_tfps_subproof g).

Lemma map_tfpsM g h : map_tfps (g * h) = (map_tfps g) * (map_tfps h).
Proof.
apply/tfpsP => i Hi.
rewrite coef_map /= !coefM_tfps Hi rmorph_sum.
apply eq_bigr => [] [j]; rewrite /= ltnS => le_ji _.
by rewrite rmorphM !coef_map.
Qed.

Fact map_tfps_is_additive : additive map_tfps.
Proof. by move => x y; apply/tfps_inj => /=; rewrite rmorphB. Qed.
Canonical map_tfps_additive := Additive map_tfps_is_additive.

Lemma map_tfpsZ (c : K) g : map_tfps (c *: g) = (f c) *: (map_tfps g).
Proof. by apply/tfpsP => i le_in; rewrite coef_tfpsE /= map_polyZ. Qed.
Canonical map_tfps_linear := let R := {tfps K n} in
  AddLinear (map_tfpsZ : scalable_for (f \; *:%R) map_tfps).

Fact map_tfps_is_multiplicative : multiplicative map_tfps.
Proof.
split => [x y|]; first by rewrite map_tfpsM.
by apply/tfps_inj => /=; rewrite rmorph1.
Qed.
Canonical map_tfps_rmorphism := AddRMorphism map_tfps_is_multiplicative.
Canonical map_tfps_lrmorphism := [lrmorphism of map_tfps].


(* Tests *)
Fact test_map_tfps0 : map_tfps 0 = 0.
Proof. by rewrite linear0. Qed.

Fact test_map_tfpsD g h :
  map_tfps (g + h) = (map_tfps g) + (map_tfps h).
Proof. by rewrite linearD. Qed.


Lemma trXn_map_poly (p : {poly K}) :
  @trXn L n (map_poly f p) = map_tfps (trXn n p).
Proof. by apply/tfpsP => i le_in; rewrite !(coef_trXn, le_in, coef_map). Qed.

Local Notation "g '^f'" := (map_tfps g).
Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma map_hmul g h : (g *h h) ^f = (g ^f) *h (h ^f).
Proof.
apply/tfpsP => i le_in /=.
rewrite coef_map !coef_poly ltnS le_in [LHS]rmorphM.
have co (l : {tfps K n}) : (if i < size l then f l`_i else 0) = f l`_i.
  by case: ltnP => // H; rewrite nth_default // rmorph0.
by rewrite !co.
Qed.

End MapTFPS.

Lemma map_tfps_injective (K L : ringType) n (f : {injmorphism K -> L}) :
  injective (@map_tfps _ _ n f).
Proof.
by move=> x y /val_eqP/eqP /= /map_poly_injective H; apply tfps_inj.
Qed.

Lemma map_tfps_inj (K : fieldType) (L : ringType) n (f : {rmorphism K -> L}) :
  injective (@map_tfps _ _ n f).
Proof. by move=> x y /val_eqP/eqP /= /map_poly_inj H; apply tfps_inj. Qed.

Lemma trXnt_map_poly (m n : nat) (K L : ringType)
      (f : {rmorphism K -> L}) (g : {tfps K n}) :
  trXnt m (map_tfps f g) = map_tfps f (trXnt m g).
Proof. by apply/tfpsP=> i le_in; rewrite !(coef_map, coef_trXn) le_in. Qed.

Lemma map_poly_idfun (R : ringType) : map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma idfun_injective A : injective (@idfun A). Proof. done. Qed.
Canonical idfun_is_injmorphism (A : ringType) :=
    InjMorphism (@idfun_injective A).

Lemma map_tfps_idfun (K : fieldType) (m : nat) :
  map_tfps [rmorphism of (@idfun K)] =1 @idfun {tfps K m}.
Proof.
move=> f; apply/tfpsP => i le_in /=.
by rewrite coef_tfpsE /= map_poly_idfun.
Qed.


Section Coefficient01.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition coef0_eq0 := fun f : {tfps R n} => f`_0 == 0.
Definition coef0_eq1 := fun f : {tfps R n} => f`_0 == 1.

Lemma coef0_eq0E f : (f \in coef0_eq0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Lemma coef0_eq1E f : (f \in coef0_eq1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Fact c0_is_0_idealr : idealr_closed coef0_eq0.
Proof.
split => [|| a p q ]; rewrite ?coef0_eq0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefD q0_eq0 addr0 coef0_tfpsM p0_eq0 mulr0.
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

Lemma tfpsX_in_coef0_eq0 : \X \in coef0_eq0.
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
by rewrite coef0_tfpsM; move/eqP ->; move/eqP ->; rewrite mul1r.
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

Lemma coef0_eq0_trXnt (R : ringType) (n m : nat) (f : {tfps (R) n}) :
  (trXnt m f \in coef0_eq0) = (f \in coef0_eq0).
Proof. by rewrite !coef0_eq0E coef0_trXn. Qed.

Lemma coef0_eq1_trXnt (R : ringType) (n m : nat) (f : {tfps (R) n}) :
  (trXnt m f \in coef0_eq1) = (f \in coef0_eq1).
Proof. by rewrite !coef0_eq1E coef0_trXn. Qed.


Section Coefficient01Unit.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact invr_closed_c0_is_1 : invr_closed (@coef0_eq1 R n).
Proof.
move=> f; rewrite !coef0_eq1E coef0_tfpsV; move/eqP ->.
by rewrite invr1.
Qed.
Canonical c0_is_1_DivrPred := DivrPred invr_closed_c0_is_1.

Example coef0_eq1V f : f \in coef0_eq1 -> f^-1 \in coef0_eq1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Example coef0_eq1_div f g :
  f \in coef0_eq1 -> g \in coef0_eq1 -> f / g \in coef0_eq1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.

Lemma coef0_eq1_unit f : f \in coef0_eq1 -> f \is a GRing.unit.
Proof. by rewrite !coef0_eq1E unit_tfpsE => /eqP ->; apply unitr1. Qed.

End Coefficient01Unit.


Section Coefficient01IDomain.

Variables (R : idomainType) (n : nat).
Implicit Types (f g : {tfps R n}).

Fact c0_is_0_prime : prime_idealr_closed (@coef0_eq0 R n).
Proof.
by move => x y; rewrite -!topredE /= /coef0_eq0 coef0_tfpsM mulf_eq0.
Qed.
Canonical coef0_eq0_pideal := MkPrimeIdeal (c0_is_0_ideal R n) c0_is_0_prime.

Example coef0_eq0_prime_test f g :
  f * g \in coef0_eq0 -> (f \in coef0_eq0) || (g \in coef0_eq0).
Proof. by rewrite prime_idealrM. Qed.

End Coefficient01IDomain.


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
apply/tfpsP => i le_in; rewrite coef_trXn coef0 le_in.
by rewrite coefX_eq0 // (leq_ltn_trans le_in H2).
Qed.

Lemma trXnMX_eq0 n p q i j :
  p`_0 = 0 -> q`_0 = 0 -> n < i + j -> trXn n (p ^+ i * q ^+ j) = 0.
Proof.
move=> p0 q0 lt_n_addij.
apply/tfpsP => l le_li; rewrite coef0.
rewrite coef_trXn le_li coefM.
rewrite (bigID (fun k => val k >= i)) /= ?big1 ?addr0 // => [] [k Hk] /= H.
- rewrite -ltnNge in H.
  by rewrite coefX_eq0 ?mul0r.
- rewrite ltnS in Hk.
  rewrite [X in _* X]coefX_eq0 ?mulr0 //.
  rewrite leq_ltn_subLR //.
  exact: (leq_ltn_trans le_li (leq_trans lt_n_addij (leq_add _ _))).
Qed.

Lemma coefX_tfps_eq0 n m i :
  i < m -> {in coef0_eq0, forall f : {tfps R n}, (f ^+ m)`_i = 0}.
Proof.
move=> lt_im f; rewrite coef0_eq0E => /eqP/coefX_eq0/(_ lt_im).
by rewrite coef_tfpsE !exp_tfps_val coef_trXn => ->; rewrite if_same.
Qed.

Lemma tfpsX_eq0 (n m : nat) :
  n < m -> {in coef0_eq0, forall f : {tfps R n}, f ^+ m = 0}.
Proof.
move=> le_nm f /coefX_tfps_eq0 H0.
apply/tfpsP => i le_in.
by rewrite coef_tfps0 H0 // (leq_ltn_trans le_in le_nm).
Qed.

Lemma tfpsMX_eq0 n i j : n < i + j ->
  {in @coef0_eq0 R n &, forall f g, f ^+ i * g ^+ j = 0}.
Proof.
move=> lt_n_addij f g f0 g0.
apply tfps_inj.
rewrite mul_tfps_val !exp_tfps_val trXn_mul.
by rewrite trXnMX_eq0 //= -/(_`_0) ?(eqP f0) ?(eqP g0).
Qed.

End MoreExpPoly.


Section GeometricSeries.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma geometricMl f :
  f \in coef0_eq0 -> (1 - f) * (\sum_(i < n.+1) f ^+ i) = 1.
Proof.
move=> f0_eq0.
have:= telescope_sumr (fun i => f ^+ i) (leq0n n.+1).
rewrite big_mkord expr0 tfpsX_eq0 // sub0r => /(congr1 (fun x => -x)).
rewrite opprK => {2}<-.
rewrite mulr_sumr -sumrN; apply eq_bigr => /= i _.
by rewrite opprB mulrBl mul1r -exprS.
Qed.

Lemma geometricMr f :
  f \in coef0_eq0 -> (\sum_(i < n.+1) f ^+ i) * (1 - f) = 1.
Proof.
move=> /geometricMl {2}<-; apply/commr_sym/commr_sum => i _.
apply/commr_sym/commrB; do [exact:commr1 |].
by apply/commr_sym/commrX.
Qed.

End GeometricSeries.


Section GeometricSeriesUnit.

Variables (R : unitRingType) (n : nat).
Implicit Types (c : R) (f g : {tfps R n}).

Lemma geometricV f :
  f \in coef0_eq0 -> (1 - f) ^-1 = \sum_(i < n.+1) f ^+ i.
Proof.
move=> f0_eq0.
have f1unit : 1 - f \is a GRing.unit.
  by apply: coef0_eq1_unit; rewrite -coef0_eq01 rpredN.
by apply: (mulrI f1unit); rewrite geometricMl // divrr.
Qed.

Lemma geometric_1cNV c :
  (1 - c *: \Xo(n))^-1 = \sum_(i < n.+1) (c *: \X) ^+ i.
Proof. exact/geometricV/coef0_eq0Z/tfpsX_in_coef0_eq0. Qed.

Lemma coeff_geometric_1cNV c m :
  m <= n -> ((1 - c *: \Xo(n))^-1)`_m = c ^+ m.
Proof.
rewrite geometric_1cNV coeft_sum -ltnS => lt_mn1.
rewrite (bigD1 (Ordinal lt_mn1)) //=.
rewrite expr_cX coeftZ coef_tfpsXn -ltnS lt_mn1 eqxx mulr1 big1 ?addr0 // => i.
rewrite -val_eqE /= => /negbTE eq_imF.
by rewrite expr_cX coeftZ coef_tfpsXn eq_sym eq_imF andbF mulr0.
Qed.

Lemma coeff_geometric_1cV c m :
  m <= n -> ((1 + c *: \Xo(n))^-1)`_m = (-c) ^+ m.
Proof. by rewrite -{1}[c]opprK scaleNr; apply: coeff_geometric_1cNV. Qed.

End GeometricSeriesUnit.


Section DivisionByX.

Variable R : ringType.

Definition mulfX m (f : {tfps R m}) :=
  [tfps i <= m.+1 => if i == 0%N then 0 else f`_i.-1].
Definition divfX m (f : {tfps R m}) :=
  [tfps i <= m.-1 => f`_i.+1].

Lemma coef_mulfX m (f : {tfps R m}) i :
  (mulfX f)`_i = if i == 0%N then 0 else f`_i.-1.
Proof.
rewrite coef_tfps_of_fun; case: i => //= i.
rewrite ltnS; case: leqP => // lt_mi.
by rewrite nth_default // (leq_trans (size_tfps f) lt_mi).
Qed.
Lemma coef_divfX m (f : {tfps R m}) i : (divfX f)`_i = f`_i.+1.
Proof.
rewrite coef_tfps_of_fun; case: leqP => // Hi.
rewrite nth_default // (leq_trans (size_tfps f)) //.
by move: Hi; case m.
Qed.

Lemma mulfXK m : cancel (@mulfX m) (@divfX m.+1).
Proof.
move=> p; apply/tfpsP => i Hi.
by rewrite coef_divfX coef_mulfX.
Qed.

Lemma divfXK m : {in coef0_eq0, cancel (@divfX m.+1) (@mulfX m)}.
Proof.
move=> p Hp.
by apply/tfpsP => [[|i]] Hi; rewrite coef_mulfX coef_divfX // (eqP Hp).
Qed.

Lemma mulfX1 m : mulfX 1 = \X :> {tfps R m.+1}.
Proof.
by apply/tfpsP => [] [|[|i]] _;
  rewrite coef_mulfX coef_tfpsX // ?coef_tfps1 ?mulr1 ?mulr0.
Qed.
Lemma divfXX m : divfX (\X : {tfps R m.+1}) = 1 :> {tfps R m}.
Proof. by rewrite -[RHS]mulfXK mulfX1. Qed.

Fact mulfX_is_linear m : linear (@mulfX m).
Proof.
move=> c f g; apply/tfpsP => i _; rewrite !(coeftD, coeftZ, coef_mulfX).
by case: eqP => //; rewrite mulr0 add0r.
Qed.
Canonical mulfX_additive m := Additive (@mulfX_is_linear m).
Canonical mulfX_linear m := Linear (@mulfX_is_linear m).

Fact divfX_is_linear m : linear (@divfX m).
Proof.
by move=> c f g; apply/tfpsP => i _; rewrite !(coeftD, coeftZ, coef_divfX).
Qed.
Canonical divfX_additive m := Additive (@divfX_is_linear m).
Canonical divfX_linear m := Linear (@divfX_is_linear m).


Variable m : nat.
Implicit Type f : {tfps R m}.

Lemma trXn_mulfXE f : trXn m (tfps (mulfX f)) = \X * f.
Proof.
apply/tfpsP => i Hi.
by rewrite coef_trXn coef_mulfX coef_tfpsXM Hi.
Qed.

Lemma mulfXE f : mulfX f = \X * trXnt m.+1 f.
Proof.
apply/tfpsP => i Hi.
rewrite coef_mulfX coef_tfpsXM coef_trXnt Hi.
by case: i Hi => //= i /ltnW ->.
Qed.

Lemma trXnt_mulfX f n :
  n <= m -> trXnt n.+1 (mulfX f) = mulfX (trXnt n f).
Proof.
move=> le_nm; apply/tfpsP => i le_in1.
rewrite coef_trXnt !coef_mulfX le_in1.
by case: i le_in1 => //= i; rewrite ltnS coef_trXnt => ->.
Qed.

Lemma mulfXM f (g : {tfps R m.+1}) : (mulfX f) * g = mulfX (f * trXnt m g).
Proof.
apply/tfpsP => [[|i]].
  by rewrite !(coef0_tfpsM, coef_mulfX, coef0_trXn, coef_tfpsE) /= mul0r.
rewrite ltnS => le_im.
rewrite coef_mulfX /= -/(_`_i.+1) !coefM_tfps ltnS le_im.
rewrite big_ord_recl /= -/(_`_0) coef_mulfX /= mul0r add0r.
apply eq_bigr => [[j] /=]; rewrite ltnS => le_ji _.
rewrite -/(_`_j.+1) coef_mulfX /= /bump /= add1n subSS.
by rewrite coef_trXnt (leq_trans (leq_subr _ _) le_im).
Qed.

Lemma coef_mulfX_exp_lt f i j : i < j -> (mulfX f ^+ j)`_i = 0.
Proof.
elim: j i => [|j IHj] i //; rewrite ltnS => le_ij.
rewrite exprS coefM_tfps; case leqP => // _.
rewrite big_ord_recl big1 ?coef_mulfX ?mul0r ?add0r // => [[u /=]] lt_ui _.
rewrite {}IHj ?mulr0 // /bump /= add1n.
case: i lt_ui le_ij => // i _ lt_ij.
by rewrite subSS (leq_ltn_trans (leq_subr _ _) lt_ij).
Qed.

Lemma coef_mulfX_exp f i : i <= m.+1 -> (mulfX f ^+ i)`_i = (f ^+ i)`_0.
Proof.
elim: i => [|i IHi] lt_im1; first by rewrite !expr0 coef1.
rewrite exprS coefM_tfps (leq_trans lt_im1 _) //.
rewrite big_ord_recl coef_mulfX mul0r add0r.
rewrite big_ord_recl coef_mulfX /= /bump /= add1n subSS subn0.
rewrite {}IHi ?(ltnW lt_im1) // -!/(_`_0).
rewrite -coef0_tfpsM ?rpredX // -exprS.
rewrite big1 ?addr0 // => [[j /= lt_ji]] _.
rewrite !add1n subSS coef_mulfX_exp_lt ?mulr0 //.
case: i lt_ji {lt_im1} => // i.
by rewrite !ltnS subSS leq_subr.
Qed.

End DivisionByX.

Lemma divfXE (K : idomainType) m :
  {in @coef0_eq0 K m, forall f, divfX f = trXn m.-1 (tfps f %/ 'X)}.
Proof.
move=> f.
move/eqP/polyXP; rewrite Pdiv.IdomainUnit.dvdp_eq ?lead_coefX ?unitr1 //.
rewrite /divfX; move/eqP => h; apply/tfpsP => i Hi.
by rewrite coef_poly coef_trXn ltnS Hi coef_tfpsE [in LHS]h coefMX.
Qed.

Lemma map_tfps_mulfX (K L : ringType) (f : {rmorphism K -> L})
  (m : nat) (g : {tfps K m}) :
  map_tfps f (mulfX g) = mulfX (map_tfps f g).
Proof.
apply/tfpsP => i lt_im1.
rewrite !(coef_mulfX, coef_map, lt_im1).
by case: i {lt_im1}=> [|j]//=; rewrite rmorph0.
Qed.

Lemma map_tfps_divfX (K L : ringType) (f : {rmorphism K -> L})
  (m : nat) (g : {tfps K m}) :
  map_tfps f (divfX g) = divfX (map_tfps f g).
Proof.
apply/tfpsP => i lt_im1.
by rewrite !(coef_divfX, coef_map, lt_im1).
Qed.


Section Derivative.

Variables (R : ringType) (n : nat).
Implicit Types (f g : {tfps R n}).

Lemma deriv_trXn (p : {poly R}) :
  (tfps (trXn n.+1 p))^`() = tfps (trXn n (p^`())).
Proof.
apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv ltnS.
by case: leqP => //; rewrite mul0rn.
Qed.

Fact trXn_deriv (m : nat) (f : {tfps R n}) : n <= m ->
  tfps (trXn m (tfps f)^`()) = (tfps f)^`().
Proof.
move => le_nm; apply/polyP => i /=.
rewrite coef_deriv !coef_trXn coef_deriv.
case: leqP => lt_mi //.
by rewrite coef_tfps (leq_gtF (ltnW (leq_ltn_trans le_nm lt_mi))) mul0rn.
Qed.

Definition deriv_tfps f := [tfps j <= n.-1 => f`_j.+1 *+ j.+1].
Local Notation "f ^` () " := (deriv_tfps f) : tfps_scope.

Lemma coef_deriv_tfps f j :
  (deriv_tfps f)`_j = f`_j.+1 *+ j.+1.
Proof.
rewrite coef_tfps_of_fun; case: leqP => //.
rewrite coef_tfps [j < n]ltnNge.
by case: n f => /= [|m f ->]; rewrite mul0rn.
Qed.

Lemma val_deriv_tfps f : tfps (deriv_tfps f) = (tfps f)^`()%R.
Proof. by apply/polyP => i; rewrite coef_deriv_tfps coef_deriv. Qed.

Lemma deriv_tfpsE f : deriv_tfps f = trXn n.-1 (tfps f)^`().
Proof. by rewrite -val_deriv_tfps tfpsK. Qed.

Fact deriv_tfps0 : (0 : {tfps R n})^`() = 0.
Proof. by apply tfps_inj; rewrite val_deriv_tfps deriv0. Qed.

Lemma deriv_tfpsC (c : R) : c%:S^`() = 0.
Proof. by apply tfps_inj; rewrite val_deriv_tfps /= val_tfpsC derivC. Qed.

Lemma deriv_tfps1 : 1^`() = 0.
Proof. by rewrite -tfpsC1 deriv_tfpsC. Qed.

Fact deriv_tfpsD f g : (f + g)^`() = f^`()%tfps + g^`()%tfps.
Proof.
apply/tfpsP => i le_in1.
by rewrite coefD !coef_poly ltnS le_in1 coefD -mulrnDl.
Qed.

Fact deriv_tfpsZ (c : R) f : (c *: f)^`() = c *: f^`()%tfps.
Proof.
apply/tfpsP => i le_in1.
by rewrite !(coef_poly, coefZ) ltnS le_in1 mulrnAr.
Qed.

Fact deriv_tfps_is_linear : linear deriv_tfps.
Proof. by move => c f g; rewrite deriv_tfpsD deriv_tfpsZ. Qed.
Canonical deriv_tfps_additive := Additive deriv_tfps_is_linear.
Canonical deriv_tfps_linear := Linear deriv_tfps_is_linear.

(* Tests *)
Example test_deriv_tfps0 : 0^`() = 0.
Proof. by rewrite linear0. Qed.

Example test_deriv_tfpsD f g :
  (f + g)^`() = f^`()%tfps + g^`()%tfps.
Proof. by rewrite linearD. Qed.

End Derivative.

Notation "f ^` () " := (deriv_tfps f) : tfps_scope.


Section MoreDerivative.

Variables (R : ringType).

Lemma deriv_tfpsX n : \Xo(n.+1)^`() = 1  :> {tfps R n}.
Proof. by rewrite deriv_tfpsE val_tfpsX scale1r derivX trXn1. Qed.

Lemma deriv_trXnt m n (p : {tfps R m}) :
  (trXnt n.+1 p)^`()%tfps = trXnt n (p^`())%tfps.
Proof.
rewrite /trXnt deriv_tfpsE deriv_trXn [n.+1.-1]/= trXn_trXn //.
by rewrite -val_deriv_tfps.
Qed.

Lemma deriv_tfps0p (f : {tfps R 0}) : f^`() = 0.
Proof. by rewrite [f]tfps_is_cst deriv_tfpsC. Qed.

Theorem derivM_tfps n (f g : {tfps R n}) :
  (f * g)^`() = f^`()%tfps * (trXnt n.-1 g) + (trXnt n.-1 f) * g^`()%tfps.
Proof.
move: f g; case: n => /= [f g | m f g].
  rewrite [f]tfps_is_cst [g]tfps_is_cst -tfpsCM !deriv_tfpsC.
  by rewrite mul0r mulr0 addr0.
apply/tfps_inj; rewrite !deriv_tfpsE deriv_trXn /=.
by rewrite trXn_trXn // derivM rmorphD !rmorphM.
Qed.

(* Noncommutative version *)
Theorem derivX_tfps_nc n (f : {tfps R n}) k :
  (f ^+ k)^`() =
  \sum_(i < k) (trXnt n.-1 f) ^+ i * (f^`())%tfps * (trXnt n.-1 f) ^+ (k.-1-i).
Proof.
have Hn := leq_pred n.
case: k; first by rewrite !expr0 deriv_tfps1 big_ord0.
elim=> [|k IHk] /=.
  by rewrite !expr1 big_ord_recl big_ord0 addr0 subnn expr0 mul1r mulr1.
rewrite exprS derivM_tfps big_ord_recl subn0 expr0 mul1r rmorphX /=.
congr (_ + _).
rewrite {}IHk mulr_sumr; apply eq_bigr => i _.
by rewrite /bump /= add1n subSS !mulrA -exprS.
Qed.

End MoreDerivative.


Section DerivativeComRing.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {tfps R n}).


Theorem derivX_tfps f k :
  (f ^+ k)^`() = (trXnt n.-1 f) ^+ (k.-1) * (f^`())%tfps *+ k.
Proof.
have Hn := leq_pred n.
rewrite derivX_tfps_nc -{9}(card_ord k) -sumr_const.
apply eq_bigr => [] [i /= Hi] _.
by rewrite mulrC mulrA -!rmorphX -rmorphM /= -exprD subnK //; case: k Hi.
Qed.

Theorem derivX_tfps_bis f k :
  (f ^+ k)^`() = (f^`())%tfps * (trXnt n.-1 f) ^+ (k.-1) *+ k.
Proof. by rewrite derivX_tfps mulrC. Qed.

End DerivativeComRing.


Section DerivativeUnitRing.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

(* Noncommutative version *)
Theorem derivV_tfps_nc f :
  f \is a GRing.unit ->
  (f ^-1)^`() = - trXnt n.-1 (f^-1) * (f^`()%tfps) * trXnt n.-1 (f^-1).
Proof.
move => fU.
have:= erefl (f / f); rewrite {2}divrr //.
move/(congr1 (@deriv_tfps R n)).
rewrite derivM_tfps -tfpsC1 deriv_tfpsC.
(* Coq is confused with the pattern matching :-( ?? Let's help him ! *)
move/eqP; rewrite addrC; set X := (X in X + _); rewrite (addr_eq0 X _) {}/X.
move/eqP/(congr1 (fun x => (trXnt n.-1 f ^-1) * x)).
rewrite {1}trXntV ?leq_pred // mulKr ?(mulrN, mulNr, mulrA) //.
by rewrite unit_tfpsE coef0_trXn.
Qed.

End DerivativeUnitRing.


Section DerivativeComUnitRing.

Variables (R : comUnitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Theorem derivV_tfps f :
  f \is a GRing.unit -> (f ^-1)^`() = - (f^`()%tfps) / trXnt n.-1 (f ^+ 2).
Proof.
move=> fU.
rewrite derivV_tfps_nc // -mulrA mulrC -mulrA !mulrN mulNr.
rewrite trXntV ?leq_pred // -invrM ?unit_tfpsE ?coef0_trXn //.
by rewrite -{1}rmorphM ?leq_pred.
Qed.

Theorem deriv_div_tfps f g :
  g \is a GRing.unit ->
  (f / g)^`() = (f^`()%tfps * trXnt n.-1 g - trXnt n.-1 f * g^`()%tfps)
                                                    / (trXnt n.-1 (g ^+ 2)).
Proof.
move => fU.
rewrite derivM_tfps derivV_tfps // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
rewrite trXntV ?leq_pred // expr2 ?leq_pred //.
rewrite rmorphM ?leq_pred //= => Hn.
by rewrite invrM ?mulrA ?divrr ?div1r // trXnt_unitE.
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


Implicit Types (f g : {tfps R n}).

Lemma size_prim_leq f : size (prim (tfps f)) <= n.+2.
Proof.
apply: (leq_trans (size_poly _ _) _); rewrite ltnS.
exact: size_tfps.
Qed.
Definition prim_tfps f := Tfps_of (size_prim_leq f).

Lemma coef_prim_tfps f i : (prim_tfps f)`_i = (prim (tfps f))`_i.
Proof. by []. Qed.

Fact prim_tfps_is_linear : linear prim_tfps.
Proof.
move=> k p q; apply/tfpsP => i lt_in1.
rewrite coefD coefZ !coef_prim.
case: i lt_in1 => [|i]/=; first by rewrite mulr0 addr0.
rewrite ltnS => lt_in.
by rewrite coefD coefZ mulrDl mulrA.
Qed.
Canonical prim_tfps_additive := Additive prim_tfps_is_linear.
Canonical prim_tfps_linear := Linear prim_tfps_is_linear.

(* tests *)
Example prim_tfps0 : prim_tfps 0 = 0.
Proof. exact: linear0. Qed.

Example prim_tfpsD : {morph prim_tfps : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma coef0_prim_tfps f : (prim_tfps f)`_0 = 0.
Proof. by rewrite coef_poly eqxx mulr0n invr0 mulr0. Qed.

End Primitive.


Section MoreCompPoly.

Variable (R : ringType).
Implicit Type (p q : {poly R}).

Lemma trXn_comp_polyr n p q :
  trXn n (p \Po q) = trXn n (p \Po (tfps (trXn n q))).
Proof.
apply/trXnP => i le_in.
rewrite !coef_comp_poly; apply eq_bigr => j _; congr (_ * _).
have /= := (congr1 (fun x => (tfps x)`_i) (exp_tfps_val (trXn n q) j)).
rewrite !coef_trXn le_in => <-.
by rewrite -rmorphX coef_trXn le_in.
Qed.

Lemma trXn_comp_polyl n p q :
  q`_0 = 0 -> trXn n (p \Po q) = trXn n ((tfps (trXn n p)) \Po q).
Proof.
move => q0_eq0; apply/trXnP => i le_in.
rewrite -{1}(poly_cat p n.+1) comp_polyD coefD !trXnE.
rewrite [X in _ + X](_ : _ = 0) ?addr0 //.
rewrite coef_comp_poly; apply big1 => [] [j /=] le_jsz _.
rewrite coefXnM; case: ltnP => [] Hi; first by rewrite mul0r.
by rewrite coefX_eq0 ?mulr0 // (leq_ltn_trans le_in Hi).
Qed.

End MoreCompPoly.


Section Composition.

Variables (R : ringType) (n : nat).

Definition comp_tfps m (f g : {tfps R m}) :=
  if f \in coef0_eq0
  then trXn m (tfps g \Po tfps f)
  else (g`_0%N)%:S.  (* avoid particular cases (e.g. associatvity) *)

Local Notation "f \So g" := (comp_tfps g f) : tfps_scope.


Lemma comp_tfps_coef0_neq0 m (f g : {tfps R m}) :
  g \notin coef0_eq0 -> f \So g = (f`_0%N)%:S.
Proof. by move/negbTE => p0_neq0; rewrite /comp_tfps p0_neq0. Qed.

Lemma comp_tfps_coef0_eq0 m (f g : {tfps R m}) :
  g \in coef0_eq0 -> f \So g = trXn m (tfps f \Po tfps g).
Proof. by move => f0_eq0 ; rewrite /comp_tfps f0_eq0. Qed.

Lemma comp_tfps0r m (f : {tfps R m}) : f \So 0 = (f`_0)%:S.
Proof.
rewrite comp_tfps_coef0_eq0 ?rpred0 // comp_poly0r.
by rewrite -tfpsCE -coef_tfpsE.
Qed.

Lemma comp_tfps0l m (f : {tfps R m}) : 0 \So f = 0.
Proof.
case (boolP (f \in coef0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_tfps_coef0_eq0 // comp_poly0 rmorph0.
- by rewrite comp_tfps_coef0_neq0 // coef_tfps0 tfpsC0.
Qed.

Implicit Types (f g h : {tfps R n}) (p q : {poly R}).

Lemma coef0_comp_tfps f g : (f \So g)`_0 = f`_0.
Proof.
rewrite /comp_tfps; case: (boolP (_ \in _)); last by rewrite coef_tfpsC.
rewrite coef0_eq0E coef_trXn {-2}[0%N]lock /= -lock => /eqP g0_eq0.
rewrite coef_comp_poly.
case Hsz : (size (tfps f)) => [|sz].
  by rewrite big_ord0 nth_default // leqn0 size_tfpsE Hsz.
rewrite big_ord_recl big1.
- by rewrite addr0 -coef_tfpsE expr0 coef1 mulr1.
- move=> [i /= Hi] _.
  by rewrite /bump /= -/(_`_0) add1n exprSr coef0M -coef_tfpsE g0_eq0 !mulr0.
Qed.

Lemma coef_comp_tfps k f g :
  g \in coef0_eq0 -> (f \So g)`_k = \sum_(i < k.+1) f`_i * (g ^+ i)`_k.
Proof.
move=> g0; rewrite (comp_tfps_coef0_eq0 _ g0).
rewrite coef_trXn; case: leqP => [le_kn | lt_nk].
- rewrite coef_comp_poly.
  have co_is0 i : minn (size f) k.+1 <= i -> f`_i * (g ^+ i)`_k = 0.
    rewrite geq_min => /orP [/(nth_default _) ->| lt_ki]; first by rewrite mul0r.
    rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
    by rewrite coefX_eq0 ?mulr0 ?(eqP g0).
  rewrite [RHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
  rewrite [LHS](bigID (fun i : 'I_ _ => i < minn (size f) k.+1)) /=.
  rewrite [X in _ + X]big1 ?addr0; first last.
    move=> [i /=] _; rewrite -leqNgt => /co_is0 /=.
    by rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
  rewrite [X in _ + X]big1 ?addr0; first last.
    by move=> [i /=] _; rewrite -leqNgt => /co_is0.
  rewrite -(big_ord_widen _ (fun i => f`_i * (g ^+ i)`_k)) ?geq_minr //.
  rewrite -(big_ord_widen _ (fun i => f`_i * (tfps g ^+ i)`_k)) ?geq_minl //.
  by apply eq_bigr => i _; rewrite !coef_tfpsE !exp_tfps_val coef_trXn le_kn.
- apply/esym/big1 => [[l /=]]; rewrite ltnS => Hl _.
  by rewrite [_`_k]coef_tfps /= (ltn_geF lt_nk) mulr0.
Qed.

Lemma trXnt_comp m f g :
  m <= n -> trXnt m (f \So g) = (trXnt m f) \So (trXnt m g).
Proof.
case (boolP (g \in coef0_eq0)) => [g0_eq0 | g0_neq0] le_mn.
- rewrite !comp_tfps_coef0_eq0 ?coef0_eq0_trXnt //.
  rewrite /trXnt -trXn_comp_polyr -trXn_comp_polyl ?(eqP g0_eq0) //=.
  by rewrite trXn_trXn.
- rewrite !comp_tfps_coef0_neq0 ?coef0_eq0_trXnt //.
  by rewrite trXntC coef_trXn.
Qed.

Lemma coef0_eq0_comp f g : (f \So g \in coef0_eq0) = (f \in coef0_eq0).
Proof. by rewrite !coef0_eq0E coef0_comp_tfps. Qed.

Lemma coef0_eq1_comp f g : (f \So g \in coef0_eq1) = (f \in coef0_eq1).
Proof. by rewrite !coef0_eq1E coef0_comp_tfps. Qed.

Lemma comp_tfpsC f (c : R) : c%:S \So f = c%:S.
Proof.
case (boolP (f \in coef0_eq0)) => [f0_eq0 | f0_neq0].
- by rewrite comp_tfps_coef0_eq0 //= val_tfpsC comp_polyC -tfpsCE.
- by rewrite comp_tfps_coef0_neq0 ?coef_tfpsC.
Qed.

Lemma comp_tfps1 f : 1 \So f = 1.
Proof. by rewrite -tfpsC1 comp_tfpsC. Qed.

Lemma comp_tfpsCf f (c : R) : f \So (c%:S) = (f`_0)%:S.
Proof.
have [->| c_neq0] := eqVneq c 0.
  by rewrite tfpsC0 comp_tfps0r.
by rewrite comp_tfps_coef0_neq0 // coef0_eq0E coef_tfpsC.
Qed.

Fact comp_tfps_is_linear (f : {tfps R n}) : linear (comp_tfps f).
Proof.
case: (boolP (f \in coef0_eq0)) => Hf a q r.
- by rewrite !comp_tfps_coef0_eq0 // !raddfD /= !linearZ.
- rewrite !comp_tfps_coef0_neq0 // coeftD coeftZ.
  by rewrite raddfD /= -!/(_`_0) tfpsCM -alg_tfpsC mulr_algl.
Qed.
Canonical comp_tfps_additive f := Additive (comp_tfps_is_linear f).
Canonical comp_tfps_linear f := Linear (comp_tfps_is_linear f).


Lemma comp_tfpsXr f : f \So \X = f.
Proof.
case: n f => [|n'] f.
  by rewrite tfps0X // comp_tfps0r {2}(tfps_is_cst f).
rewrite comp_tfps_coef0_eq0 ?tfpsX_in_coef0_eq0 //.
by rewrite val_tfpsSX comp_polyXr tfpsK.
Qed.

Lemma comp_tfpsX : {in coef0_eq0, forall f, \X \So f = f}.
Proof.
case: n => [|n'] f.
  rewrite tfps0X // comp_tfps0l {2}(tfps_is_cst f) => /eqP ->.
  by rewrite tfpsC0.
move=> /comp_tfps_coef0_eq0 ->.
by rewrite val_tfpsSX comp_polyX tfpsK.
Qed.

Lemma comp_tfpsXn i : {in coef0_eq0, forall f, \X ^+ i \So f = f ^+ i}.
Proof.
move=> f Hf; apply/tfpsP => j Hj.
rewrite coef_comp_tfps //.
case: (ltnP i j.+1) => [lt_ij1 | lt_ji].
- rewrite (bigD1 (Ordinal lt_ij1)) //= big1 ?addr0.
  + rewrite ltnS in lt_ij1.
    by rewrite coef_tfpsXn eqxx (leq_trans lt_ij1 Hj) mul1r.
  + move=> [k Hk]; rewrite -val_eqE /= coef_tfpsXn => /negbTE ->.
    by rewrite andbF mul0r.
- rewrite coefX_tfps_eq0 // big1 // => [] [k /=]; rewrite ltnS => Hk _.
  by rewrite coef_tfpsXn (ltn_eqF (leq_ltn_trans Hk lt_ji)) andbF mul0r.
Qed.

End Composition.

Notation "f \So g" := (comp_tfps g f) : tfps_scope.


Section CompComRing.

Variables (R : comRingType) (n : nat).
Implicit Types (f g h : {tfps R n}) (p : {poly R}).

Fact comp_tfps_is_rmorphism f : multiplicative (comp_tfps f).
Proof.
split => /= [g1 g2|]; last exact: comp_tfps1.
case: (boolP (f \in coef0_eq0)) => Hf.
- rewrite !comp_tfps_coef0_eq0 // mul_tfps_val /=.
  rewrite -trXn_comp_polyl -?coef_tfpsE ?(eqP Hf) //.
  rewrite rmorphM /= -trXn_mul /=.
  by rewrite -[RHS]tfpsK mul_tfps_val /= trXn_trXn.
- by rewrite !comp_tfps_coef0_neq0 // coef0_tfpsM -rmorphM.
Qed.

Canonical comp_tfps_rmorphism f := AddRMorphism (comp_tfps_is_rmorphism f).
Canonical comp_tfps_lrmorphism f := [lrmorphism of (comp_tfps f)].

Lemma comp_tfpsA f g h : f \So (g \So h) = (f \So g) \So h.
Proof.
case (boolP (h \in coef0_eq0)) => [h0_eq0 | h0_neq0]; first last.
  rewrite !(comp_tfps_coef0_neq0 _ h0_neq0).
  by rewrite comp_tfpsCf coef0_comp_tfps.
case (boolP (g \in coef0_eq0)) => [g0_eq0 | g0_neq0]; first last.
  by rewrite !(comp_tfps_coef0_neq0 f) ?comp_tfpsC // coef0_eq0_comp.
rewrite comp_tfps_coef0_eq0 ?coef0_eq0_comp //.
rewrite !comp_tfps_coef0_eq0 //.
rewrite -trXn_comp_polyr comp_polyA trXn_comp_polyl //.
by move: h0_eq0; rewrite coef0_eq0E => /eqP.
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

Lemma coef_comp_tfps_cX f c i : (f \So (c *: \X))`_i = c ^+ i * f`_i.
Proof.
case: n f => [|n'] f.
  rewrite coef_tfps [in RHS]coef_tfps leqn0.
  case: i => [|i] /=; last by rewrite mulr0.
  by rewrite -!/(_`_0) expr0 mul1r coef0_comp_tfps.
case: (leqP i n'.+1) => [lt_in1 | lt_n1i]; first last.
  rewrite coef_tfps (ltn_geF lt_n1i) nth_default ?mulr0 //.
  exact: (leq_trans (size_tfps f) lt_n1i).
rewrite -coef_comp_poly_cX.
rewrite comp_tfps_coef0_eq0 ?coef0_eq0Z ?tfpsX_in_coef0_eq0 //.
by rewrite coef_trXn lt_in1 linearZ /= val_tfpsX scale1r.
Qed.

Theorem deriv_tfps_comp f g :
  f \in coef0_eq0 ->
  (g \So f)^`() = (g^`()%tfps \So (trXnt n.-1 f)) * f^`()%tfps.
Proof.
rewrite !deriv_tfpsE //.
move: f g; case: n => [|m] f g f0_eq0.
  rewrite [f]tfps_is_cst [g]tfps_is_cst.
  rewrite /trXnt comp_tfpsC.
  by rewrite !val_tfpsC !derivC trXn0 mulr0.
rewrite -[RHS]tfpsK [m.+1.-1]/=.
rewrite /= !comp_tfps_coef0_eq0 ?coef0_eq0_trXnt //.
rewrite deriv_trXn !trXn_trXn // deriv_comp.
rewrite -trXn_mul /=; congr (trXn _ (_ * _)).
by rewrite -trXn_comp_polyr trXn_comp_polyl ?(eqP f0_eq0).
Qed.

End CompComRing.


Section Lagrange.

Variables R : comUnitRingType.
Variable n : nat.


Section LagrangeFixPoint.

Variable g : {tfps R n}.
Hypothesis gU : g \is a GRing.unit.


(** We iterate f := x (g o f) until fixpoint is reached. *)
(** At each step, the precision is incremented.          *)
Fixpoint lagriter o : {tfps R o} :=
  if o is o'.+1 then mulfX ((trXnt o' g) \So (lagriter o')) else 0.
Definition lagrfix := lagriter n.+1.

Lemma coef0_eq0_lagriter o : lagriter o \in coef0_eq0.
Proof.
by rewrite coef0_eq0E; case: o => [|o]; rewrite ?coef_tfps0 ?coef_mulfX.
Qed.
Lemma coef0_eq0_lagrfix : lagrfix \in coef0_eq0.
Proof. exact: coef0_eq0_lagriter. Qed.

Lemma lagrfixP : lagrfix = mulfX (g \So trXnt n lagrfix).
Proof.
rewrite /lagrfix.
suff rec o : o <= n ->
     lagriter o.+1 = mulfX (trXnt o g \So trXnt o (lagriter o.+1)).
  by rewrite [LHS](rec n (leqnn n)) trXnt_id.
elim: o => [_ | o IHo /ltnW{}/IHo IHo]; apply tfpsP => i.
  case: i => [_|i]; first by rewrite !coef_mulfX.
  rewrite ltnS leqn0 => /eqP ->.
  rewrite !coef_mulfX /= -!/(_`_0).
  by rewrite comp_tfps0r !coef_tfpsC coef0_comp_tfps.
case: i => [_|i]; first by rewrite !coef_mulfX.
rewrite ltnS => le_io1 /=.
rewrite -!/(_`_ i.+1) !coef_mulfX /= -/(lagriter o.+1) -!/(_`_ i.+1).
have lag0 := coef0_eq0_lagriter o.+1.
move: (lagriter o.+1) => LR in IHo lag0 *.
have Xlag0 : trXnt o.+1 (mulfX (trXnt o.+1 g \So LR)) \in coef0_eq0.
  by rewrite coef0_eq0E coef_trXnt coef_mulfX.
rewrite !coef_comp_tfps //; apply eq_bigr => k _; congr (_ * _).
rewrite {}[in LHS]IHo -rmorphX coef_trXnt le_io1.
set X :=  (_ ^+ k in RHS); have -> : X`_i = (trXnt o.+1 X)`_i.
  by rewrite {}/X coef_trXnt le_io1.
rewrite {}/X rmorphX /= trXnt_mulfX // trXnt_comp; last exact: leqnSn.
by rewrite trXnt_trXnt.
Qed.

Lemma lagrfix_divP : divfX lagrfix = g \So trXnt n lagrfix.
Proof. by rewrite {1}lagrfixP mulfXK. Qed.
Lemma divfX_lagrfix_unit : divfX lagrfix \is a GRing.unit.
Proof.
by rewrite lagrfix_divP unit_tfpsE coef0_comp_tfps -unit_tfpsE.
Qed.

Lemma lagrfix_inv f :
  f \in coef0_eq0 -> f = mulfX (g \So trXnt n f) -> (mulfX g^-1) \So f = \X.
Proof.
move=> f0 Heq.
have tinv0 : trXnt n f \in coef0_eq0 by rewrite coef0_eq0_trXnt.
rewrite mulfXE rmorphM /= comp_tfpsX //.
rewrite {1}Heq mulfXM trXnt_comp // trXnt_trXnt // trXnt_id.
rewrite rmorphV //= divrr ?mulfX1 //.
by rewrite unit_tfpsE coef0_comp_tfps -unit_tfpsE.
Qed.

Lemma lagrfix_invPr : (mulfX g^-1) \So lagrfix = \X.
Proof. exact: (lagrfix_inv coef0_eq0_lagrfix lagrfixP). Qed.

End LagrangeFixPoint.

Implicit Types (f g : {tfps R n.+1}).

Definition lagrunit f := (f \in coef0_eq0) && (divfX f \is a GRing.unit).
Definition lagrinv f := lagrfix (divfX f)^-1.

Lemma lagrfixE (f : {tfps R n}) : lagrfix f = lagrinv (mulfX f^-1).
Proof. by rewrite /lagrinv mulfXK invrK. Qed.

Lemma coef1_comp_tfps f g :
  f \in coef0_eq0 -> g \in coef0_eq0 -> (f \So g)`_1 = f`_1 * g`_1.
Proof.
move=> f0 g0.
rewrite coef_comp_tfps // big_ord_recl (eqP f0) mul0r add0r.
by rewrite big_ord_recl /= big_ord0 /bump /= -!/(_`_ 1) !add1n addr0.
Qed.

Lemma divfX_unitE f : (divfX f \is a GRing.unit) = (f`_1 \is a GRing.unit).
Proof. by rewrite unit_tfpsE coef_divfX. Qed.

Lemma lagrunit_comp : {in lagrunit &, forall f g, lagrunit (f \So g) }.
Proof.
rewrite /lagrunit => f g /andP [f0 f1] /andP [g0 g1].
rewrite coef0_eq0_comp f0 /=.
rewrite unit_tfpsE coef_divfX /= -/(_`_1).
by rewrite coef1_comp_tfps // unitrM -!divfX_unitE f1 g1.
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
  move=> Hinv Hid; rewrite -(comp_tfpsXr g) // -(lagrinvPr Hinv).
  by rewrite comp_tfpsA {}Hid.
apply idemp_neutral; first exact: lagrunit_comp (lagrunitV Hf) Hf.
rewrite comp_tfpsA -[X in (X \So f) = _]comp_tfpsA lagrinvPr //.
by rewrite comp_tfpsXr.
Qed.

Lemma lagrinvPr_uniq f g :
  f \in lagrunit -> f \So g = \X -> g = lagrinv f.
Proof.
move=> f_lag Heq.
have g0 : g \in coef0_eq0.
  rewrite -[_ \in _]negbK; apply/negP => H.
  move: Heq; rewrite comp_tfps_coef0_neq0 //.
  move => /(congr1 (fun s : {tfps _ _} => s`_1)).
  rewrite coef_tfpsX coef_tfpsC /= => /esym/eqP.
  by rewrite mulr1 oner_eq0.
(** Standard group theoretic argument: right inverse is uniq *)
move: Heq => /(congr1 (fun s => lagrinv f \So s)).
by rewrite comp_tfpsA lagrinvPl // comp_tfpsX // comp_tfpsXr.
Qed.

Lemma lagrinvPl_uniq f g :
  f \in lagrunit -> g \So f = \X -> g = lagrinv f.
Proof.
move=> f_lag /(congr1 (fun s => s \So lagrinv f)).
(** Standard group theoretic argument: left inverse is uniq *)
rewrite -comp_tfpsA lagrinvPr // comp_tfpsXr // comp_tfpsX //.
exact: coef0_eq0_lagrfix.
Qed.

Lemma lagrinvK : {in lagrunit, involutive lagrinv}.
Proof.
(** Standard group theoretic argument: inverse is involutive *)
move=> f Hf.
by apply/esym/lagrinvPl_uniq; [apply: lagrunitV | apply: lagrinvPr].
Qed.

Lemma lagrfix_invPl :
  {in GRing.unit, forall g : {tfps R n}, lagrfix g \So (mulfX g^-1) = \X}.
Proof.
move=> g gU.
rewrite lagrfixE; apply: lagrinvPl.
rewrite /lagrunit unfold_in coef0_eq0E coef_mulfX /= eqxx /=.
by rewrite divfX_unitE coef_mulfX /= -/(_`_0) -unit_tfpsE unitrV.
Qed.

Lemma lagrfix_uniq (g : {tfps R n}) : g \in GRing.unit ->
  forall f, f = mulfX (g \So trXnt n f) -> f = lagrfix g.
Proof.
move=> gU f Hf.
rewrite lagrfixE; apply lagrinvPr_uniq.
- by rewrite /lagrunit unfold_in coef0_eq0E coef_mulfX mulfXK unitrV /= eqxx.
- by apply: lagrfix_inv => //; rewrite Hf coef0_eq0E coef_mulfX.
Qed.

End Lagrange.


Section LagrangeTheorem.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

(* TODO: nat_unit is not needed here *)
Lemma mulfX_deriv_expE n (g : {tfps R n.+1}) i :
  (g ^+ i.+1 - mulfX (g^`())%tfps * g ^+ i)`_i.+1 = 0.
Proof.
rewrite mulfXM mulrC rmorphX /= -/(_`_i.+1).
apply (mulrI (nat_unit i)); rewrite mulr0 -!coeftZ scalerBr.
rewrite -linearZ /= !scaler_nat -(derivX_tfps g i.+1) -/(_`_i.+1).
by rewrite coeftB coef_mulfX coef_deriv_tfps /= -!/(_`_i.+1) coeftMn subrr.
Qed.

Theorem Lagrange_Bürmann_exp n (g : {tfps R n}) i k :
  g \in GRing.unit ->
  k <= i <= n.+1 -> ((lagrfix g) ^+ k)`_i *+ i = (g ^+ i)`_(i - k) *+ k.
Proof.
(* We first deal with trivial cases                                    *)
case: n g => [|n] g gU.
  rewrite /lagrfix /= (tfps_is_cst g) comp_tfps0r.
  move: gU; rewrite unit_tfpsE; move: (g`_0) => g0 {g} gU.
  rewrite trXntC coef_tfpsC /=.
  case: k => [|[|k]].
  - rewrite mulr0n expr0 coef1.
    by case: i => [|i]/= _; rewrite ?mulr0n ?mul0rn.
  - move=> /andP [le1i lei1].
    have {le1i lei1} -> : i = 1%N by apply anti_leq; rewrite le1i lei1.
    by rewrite !expr1 !mulr1n subSS coef_mulfX /=.
  - move=> /andP [leki lei1].
    by have:= leq_trans leki lei1; rewrite ltnS ltn0.
case: k i => [|k] [|i]; rewrite ?(expr0, subn0, coef1, mulr0n, mul0rn) //.
rewrite subSS !ltnS => /andP [le_ki le_in].
have Xg0 : mulfX g^-1 \in coef0_eq0 by rewrite coef0_eq0E coef_mulfX.
(* The RHS is ((\X ^+ k.+1)^`() * g ^+ i.+1)`_i                        *)
have:= congr1 (fun s => (s ^+ k.+1)^`()) (lagrfix_invPl gU).
rewrite -rmorphX /= {1}(tfps_def (lagrfix g ^+ k.+1)) rmorph_sum /=.
move: (lagrfix g ^+ k.+1) => LGRF.
rewrite raddf_sum /= derivX_tfps deriv_tfpsX mulr1 /= trXnt_tfpsX.
move=> /(congr1 (fun s => (s * g ^+ i.+1)`_i)).
rewrite mulrnAl -mulrnAr.
rewrite coef_tfpsXnM (leq_gtF le_ki) le_in coeftMn => <- {k le_ki}.
rewrite mulr_suml coeft_sum -/(_`_i.+1).
(* We extract the i.+1 term of the sum                                 *)
have Hi : i.+1 < n.+3 by rewrite ltnS (leq_ltn_trans le_in).
rewrite (bigD1 (Ordinal Hi)) //= -/(_`_i.+1).
move: (LGRF`_i.+1) => Co.
rewrite !linearZ /= -scalerAl coeftZ rmorphX /= comp_tfpsX //.
rewrite derivX_tfps /= !mulrnAl coeftMn /= mulrnAr -mulrnAl.
rewrite -mulrA coefM_tfps le_in big_ord_recr /=.
rewrite subnn coef0_tfpsM coef_deriv_tfps coef_mulfX /= -!/(_`_0) mulr1n.
rewrite {2}exprS coef0_tfpsM [g^-1`_0 * _]mulrA coef0_tfpsV //.
rewrite mulVr -?unit_tfpsE // mul1r.
rewrite -rmorphX /= coef_trXnt le_in -!/(_`_0).
rewrite coef_mulfX_exp ?(leq_trans le_in) //.
rewrite -coef0_tfpsM exprVn mulVr ?rpredX // coef1 /=.
(* All the other terms vanishe.                                        *)
rewrite !big1 ?add0r ?addr0 ?mulr1 //; first last.
  move=> [j /= lt_ji] _.
  rewrite coef_trXnt (leq_trans (ltnW lt_ji) le_in).
  by rewrite coef_mulfX_exp_lt // mul0r.
move=> [j Hj]; rewrite -val_eqE /= {Hi} => Hneq.
rewrite !linearZ /= -scalerAl coeftZ rmorphX /= comp_tfpsX //.
rewrite [X in _ * X](_ : _ = 0) ?mulr0 // {LGRF}.
(* We don't have the notion of residue. As a consequence the following *)
(* is a little bit convoluted...                                       *)
(* First, lets get rid of the first mulfX...                           *)
rewrite derivX_tfps /= mulrnAl coeftMn.
case: j Hneq Hj => // j /=; rewrite eqSS !ltnS => Hij le_jn1.
rewrite [X in X *+ _](_ : _ = 0) ?mul0rn //.
rewrite mulfXE derivM_tfps deriv_tfpsX mul1r /= deriv_trXnt.
rewrite trXnt_tfpsX trXnt_trXnt ?ltnS // trXnt_id.
rewrite -[X in _ + X]mulfXE.
rewrite -rmorphX /= exprMn_comm; last exact: (commr_sym (commr_tfpsX _)).
rewrite !rmorphM !rmorphX /= trXnt_tfpsX trXnt_trXnt // trXnt_id.
rewrite -!mulrA coef_tfpsXnM le_in; case ltnP => //= le_ji.
(* We rearange to have everything expressed in [i - j]                 *)
have {Hij le_ji} lt_ji : j < i by rewrite ltn_neqAle Hij le_ji.
rewrite mulrC -mulrA exprVn -exprB ?(leq_trans (ltnW lt_ji)) //.
rewrite (subSn (ltnW _)) // exprS mulrA mulrDl mulVr //.
move: lt_ji; rewrite -subn_gt0.
case: (i - j)%N (leq_subr j i) => // d lt_di _ {j le_jn1}.
(* We gather all the [g] and conclude                                  *)
rewrite mulfXM derivV_tfps //= -/(_`_d.+1).
rewrite !mulNr raddfN /= -/(_`_d.+1) -trXntV // -mulrA -trXntM // -!mulfXM.
rewrite mulrDl mul1r mulNr -mulrA.
rewrite {2}exprS !mulrA -[_ * g]mulrA -expr2 divrK ?unitrX //.
exact: mulfX_deriv_expE.
Qed.

Theorem coef_lagrfix n (g : {tfps R n}) i :
  g \in GRing.unit -> (lagrfix g)`_i.+1 = (g ^+ i.+1)`_i / i.+1%:R.
Proof.
move/Lagrange_Bürmann_exp => HL.
case: (ltnP i n.+1) => [lt_in1 | le_ni]; first last.
  by rewrite coef_tfps (leq_gtF le_ni) coef_tfps (ltn_geF le_ni) mul0r.
have /HL : 1 <= i.+1 <= n.+1 by rewrite lt_in1.
rewrite subSS subn0 mulr1n expr1 => <-.
by rewrite -mulr_natr mulrK.
Qed.


Theorem Lagrange_Bürmann n (g : {tfps R n}) (h : {tfps R n.+1}) i  :
  g \in GRing.unit ->
  (h \So (lagrfix g))`_i.+1 = ((h^`()%tfps * g ^+ i.+1)`_i) / i.+1%:R.
Proof.
move=> gU.
have lg0 := coef0_eq0_lagrfix g.
(* We argue by linearity from the previous statement *)
rewrite (tfps_def h) !(raddf_sum, mulr_suml, coeft_sum).
apply eq_bigr => [[k /=]]; rewrite ltnS => le_kn2 _.
rewrite !linearZ /= -/(_`_i.+1) -scalerAl !coeftZ -mulrA; congr (_ * _).
case: k le_kn2 => [_|k lt_kn2].
  (* When k = 0 the result is trivial *)
  by rewrite expr0 comp_tfps1 coef1 deriv_tfps1 mul0r coef0 mul0r.
rewrite rmorphX /= comp_tfpsX // -/(_`_i.+1).
rewrite [LHS]coef_tfps [in RHS]coef_tfps ltnS.
case: leqP => [le_in1|_]; last by rewrite mul0r.
case: (ltnP i k) => [lt_ik | le_ki].
  (* If i < k both side vanishes *)
  rewrite coefX_tfps_eq0 ?ltnS //.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  rewrite coefM_tfps le_in1; apply big1 => [[j /=]]; rewrite ltnS => le_ji _.
  rewrite coef_deriv_tfps.
  rewrite coef_tfpsXn eqSS (ltn_eqF (leq_ltn_trans le_ji lt_ik)).
  by rewrite andbF mul0rn mul0r.
(* Else we conclude by the previous theorem *)
apply (mulIr (nat_unit i)); rewrite divrK // mulr_natr.
rewrite Lagrange_Bürmann_exp //; last by rewrite !ltnS le_ki le_in1.
rewrite subSS derivX_tfps /= trXnt_tfpsX deriv_tfpsX mulr1.
rewrite mulrnAl -mulrnAr coef_tfpsXnM le_in1 (leq_gtF le_ki).
by rewrite coeftMn.
Qed.


(** This form of statement doesn't allow to compute the n.+2 coefficient *)
Theorem Lagrange_Bürmann_exp2 n (g : {tfps R n.+1}) i k :
  g \in GRing.unit ->
  k <= i <= n.+1 -> ((lagrfix g) ^+ k)`_i =
                    ((1 - mulfX (g^`()%tfps) / g) * \X ^+ k * g ^+ i)`_i.
Proof.
move=> gU.
case: k i => [|k] [|i] Hki //.
- by rewrite !expr0 !mulr1 coeftB coef0_tfpsM coef_mulfX mul0r subr0.
- rewrite !expr0 !mulr1 coef_tfps1 exprS mulrA !mulrBl mul1r.
  by rewrite divrK //= -!/(_`_i.+1) -exprS mulfX_deriv_expE.
move: Hki; rewrite !ltnS => /andP [le_ki le_in].
have le_in1 := (leq_trans le_in (leqnSn _)).
rewrite -mulrA [\X^+_ * _]mulrC mulrA mulrC !mulrBl mul1r.
rewrite (exprS g i) mulrA divrK // -exprS.
rewrite (exprS \X k) -mulrA coef_tfpsXM /= ltnS le_in -/(_`_i.+1).
apply (mulIr (nat_unit i)).
rewrite mulr_natr Lagrange_Bürmann_exp // ?ltnS ?le_ki ?le_in1 //.
have := erefl (\X ^+ k * mulfX (g ^+ i.+1))^`().
rewrite {2}mulfXE mulrA [_ * \X]mulrC -exprS.
rewrite [X in _ = X]derivM_tfps derivX_tfps /=.
rewrite trXnt_trXnt // trXnt_id trXnt_tfpsX deriv_tfpsX mulr1 mulrnAl.
move/(congr1 (fun s : {tfps R _} => s`_i)).
rewrite coeftD coeftMn [(\X^+k * _)`_i]coef_tfpsXnM le_in1 (leq_gtF le_ki).
set X := (X in _ = _ + X); move=> /(congr1 (fun s => s - X)).
rewrite addrK => <-.
rewrite {}/X deriv_trXnt [\Xo(n.+2) ^+ k.+1]exprS rmorphM /= trXnt_tfpsX.
rewrite [\X * _]mulrC -!mulrA -mulfXE rmorphX /= trXnt_tfpsX -/(_`_i.+1).
rewrite coef_deriv_tfps.
rewrite !coef_tfpsXnM le_in1 ltnS le_in1 (leq_gtF (leq_trans le_ki (leqnSn _))).
rewrite (leq_gtF le_ki) coef_mulfX -/(leq _ _) (leq_gtF le_ki).
rewrite subSn //= coeftB mulrBl mulr_natr; congr (_ - _).
rewrite mulfXM !coef_mulfX -/(leq _ _).
case: leqP; rewrite ?mul0r // => lt_ki.
by rewrite derivX_tfps /= coeftMn mulrC rmorphX /= mulr_natr.
Qed.

Theorem Lagrange_Bürmann2 n (g h : {tfps R n.+1}) i :
  g \in GRing.unit ->
  (h \So (trXnt n.+1 (lagrfix g)))`_i =
  ((1 - mulfX (g^`()%tfps) / g) * h * g ^+ i)`_i.
Proof.
move=> uG.
case: (leqP i n.+1) => [le_in1 | lt_n1i]; first last.
  by rewrite coef_tfps (ltn_geF lt_n1i) coef_tfps (ltn_geF lt_n1i).
rewrite (tfps_def h) !(raddf_sum, mulr_suml, mulr_sumr, coeft_sum) /=.
apply eq_bigr => [[k /=]]; rewrite ltnS => le_kn2 _.
rewrite !linearZ /= -mulrA mulrC -!scalerAl !coeftZ; congr (_ * _).
rewrite rmorphX /= comp_tfpsX ?coef0_eq0_trXnt ?coef0_eq0_lagrfix //.
rewrite -rmorphX coef_trXnt le_in1.
case: (leqP k i) => [le_ki | lt_ik]; first last.
  rewrite coefX_tfps_eq0 ?coef0_eq0_lagrfix //.
  by rewrite -mulrA coef_tfpsXnM lt_ik.
rewrite Lagrange_Bürmann_exp2 ?le_in1 ?andbT //.
by rewrite [in RHS]mulrC mulrA.
Qed.

End LagrangeTheorem.


Section ExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {tfps R n}).

Definition exp f : {tfps R n} :=
  if f \notin coef0_eq0 then 0 else
  \sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i.

Definition log f : {tfps R n} :=
  if f \notin coef0_eq1 then 0 else
  - \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i.

Definition expr_tfps (c : R) f := exp (c *: log f).

Lemma exp_coef0_eq0 f : f \in coef0_eq0 ->
  exp f = \sum_(i < n.+1) ((i`! %:R) ^-1) *: f ^+i.
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_eq0_val f : f \in coef0_eq0 ->
  exp f = trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (tfps f) ^+i).
Proof.
rewrite /exp => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]tfpsK !linearZ /= exp_tfps_val trXn_trXn.
Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_eq0 -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0 : exp (0 : {tfps R n}) = 1.
Proof.
apply/tfpsP => i le_in.
rewrite exp_coef0_eq0 ?rpred0 // !coeft_sum /=.
rewrite big_ord_recl /= fact0 invr1 expr0 alg_tfpsC tfpsC1.
rewrite big1 ?addr0 // => [] [j ] _ _ /=.
by rewrite /bump /= add1n expr0n /= scaler0 coef0.
Qed.

Lemma expC (c : R) : exp (c %:S) = (c == 0)%:R %:S :> {tfps R n}.
Proof.
case (boolP (c %:S \in @coef0_eq0 R n)) => [| p0N0].
- rewrite coef0_eq0E coef_tfpsC /= => /eqP ->.
  by rewrite eq_refl tfpsC0 tfpsC1 exp0.
- rewrite exp_coef0_isnt_0 //.
  move: p0N0; rewrite coef0_eq0E coef_tfpsC /= => /negbTE ->.
  by rewrite rmorph0.
Qed.

Lemma log_coef0_eq1 f : f \in coef0_eq1 ->
  log f = - \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - f) ^+i.
Proof. by rewrite /log => ->. Qed.

Lemma log_coef0_eq1_val f : f \in coef0_eq1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: (1 - val f) ^+i).
Proof.
rewrite /log => ->; rewrite /= !raddf_sum; apply eq_bigr => i _ /=.
by rewrite -[LHS]tfpsK !linearZ !linearN /= exp_tfps_val trXn_trXn.
Qed.

Lemma log_coef0_isnt_1 f : f \notin coef0_eq1 -> log f = 0.
Proof. by rewrite /log => /negPf ->. Qed.

Lemma log1 : log (1 : {tfps R n}) = 0.
Proof.
apply/tfpsP => j Hj; rewrite log_coef0_eq1 ?rpred1 // coef0 subrr.
rewrite coefN big_nat big1 ?coef0 ?oppr0 // => i /andP [Hi _].
by rewrite expr0n -[i == 0%N]negbK -lt0n Hi /= scaler0.
Qed.

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

End ExpLog.

Arguments log {R n}.
Arguments exp {R n}.

Notation "f ^^ r" := (expr_tfps r f) : tfps_scope.



Module TFPSUnitRing.

Section PrimitiveUnitRing.

Variable R : unitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

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

Implicit Types (f g : {tfps R n}).

Lemma prim_tfpsK : cancel (@prim_tfps R n) (@deriv_tfps R n.+1).
Proof.
move=> p; apply/tfpsP => i le_in.
rewrite coef_deriv_tfps coef_prim_tfps.
by rewrite -coef_deriv primK -coef_tfpsE.
Qed.

Lemma deriv_tfpsK :
  {in @coef0_eq0 R n.+1, cancel (@deriv_tfps R _) (@prim_tfps R _)}.
Proof.
move=> f; rewrite coef0_eq0E => /eqP f0_eq0.
apply/tfpsP => i _.
rewrite coef_prim_tfps coef_prim coef_deriv_tfps.
case: i => [|i]; first by rewrite eq_refl f0_eq0.
by rewrite [_.+1.-1]/= -mulr_natr mulrK.
Qed.

End PrimitiveUnitRing.


Section ExpMorph.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.


Lemma nat_unit_alg (A : unitAlgType R) i : i.+1%:R \is a @GRing.unit A.
Proof. by rewrite -scaler_nat scaler_unit ?unitr1 ?nat_unit. Qed.


Implicit Types (f g : {tfps R n}).

Lemma fact_unit m : m`!%:R \is a @GRing.unit R.
Proof. by have:= fact_gt0 m; rewrite lt0n; case: m`!. Qed.

Theorem expD : {in (@coef0_eq0 R n) &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g f0_eq0 g0_eq0 /=.
rewrite !exp_coef0_eq0 ?rpredD //.
pose FG u v := (u`! * v`!)%:R ^-1 *: (g ^+ u * f ^+ v) : {tfps R n}.
rewrite (eq_bigr
           (fun i : 'I_n.+1 => \sum_(j < i.+1) FG j (i - j)%N)); first last.
  move => [i /= _] _; rewrite exprDn.
  rewrite scaler_sumr; apply: eq_bigr => [[j]]; rewrite /= ltnS => le_ji _.
  rewrite mulrC -mulrnAl scalerAl -scaler_nat scalerA -scalerAl; congr(_ *: _).
  case: i le_ji => [|i le_ji1].
    by rewrite leqn0 => /eqP ->; rewrite fact0 bin0 mulr1 muln1.
  rewrite bin_factd //.
  rewrite natr_div ?mulKr ?fact_unit // ?natrM ?unitrM ?fact_unit //.
  by apply/dvdnP; exists 'C(i.+1, j); rewrite bin_fact.
rewrite -(triangular_index_bigop _ FG (ltnSn n)) /= {}/FG.
rewrite mulrC (big_distrl _ _ _) /=; apply eq_bigr => i _.
rewrite [RHS]mulr_sumr [RHS](bigID (fun j : 'I_n.+1 => i + j < n.+1)) /=.
rewrite [X in _ + X]big1 ?addr0; first last.
  move => j; rewrite -ltnNge ltnS => lt_nij.
  by rewrite -scalerAr -scalerAl tfpsMX_eq0 // !scaler0.
apply eq_bigr => j _.
by rewrite -scalerAr -scalerAl scalerA natrM invrM // fact_unit.
Qed.

Lemma expN f : f \in coef0_eq0 -> exp (- f) = (exp f)^-1.
Proof.
move=> f0_eq0; apply: (@mulrI _ (exp f)); rewrite ?divrr ?exp_unit //.
by rewrite -expD ?rpredN // subrr exp0.
Qed.

Lemma expB : {in (@coef0_eq0 R n) &, {morph exp : f g / f - g >-> f / g}}.
Proof. by move=> f g hf hg; rewrite expD ?rpredN // expN. Qed.

End ExpMorph.


Section MoreDerivative.

Variable R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

Implicit Types (f g : {tfps R n}).

Theorem derivXn_tfps m :
  m != 0%N ->  {in GRing.unit, forall f,
     (f ^- m)^`() = (trXnt n.-1 f) ^- m.+1 * f^`()%tfps *- m}.
Proof.
move=> Hm /= f fU; rewrite -exprVn derivX_tfps derivV_tfps //.
rewrite rmorphV ?leq_pred //= => _.
rewrite !exprVn rmorphX ?leq_pred //= => _.
rewrite [_/_]mulrC mulrA mulrN mulNrn -!mulrnAr.
rewrite -!exprVn -exprD -addSnnS addn1.
by case: m Hm.
Qed.

Lemma deriv_tfps_eq0_cst f : f^`() = 0 -> {c : R | f = c %:S}.
Proof.
move: f; case: n => [f _| m f H]; exists (f`_0).
  by rewrite {1}[f]tfps_is_cst.
apply/tfpsP => [] [|i]; rewrite coef_tfpsC // ltnS [RHS]/= => le_im.
apply: (mulIr (nat_unit i)); rewrite mul0r.
move: H => /(congr1 (fun x : {tfps _ _ } => x`_i)).
by rewrite coef_deriv_tfps coef0 -mulr_natr.
Qed.

Lemma deriv_tfps_ex_eq0 f :
  f^`() = 0 -> {x : R | (tfps f).[x] = 0} -> f = 0.
Proof.
move=> /deriv_tfps_eq0_cst [c ->] [x].
rewrite val_tfpsC /= hornerC => ->.
by rewrite tfpsC0.
Qed.

Lemma deriv_tfps_eq0 f : f^`() = 0 -> f`_0 = 0 -> f = 0.
Proof.
move=> /deriv_tfps_ex_eq0 H f0_eq0; apply: H.
by exists 0; rewrite horner_coef0.
Qed.

Lemma deriv_tfps_ex_eq f g :
  f^`() = g^`() -> {x : R | (tfps f).[x] = (tfps g).[x]} -> f = g.
Proof.
move=> H [x Hx].
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_tfps_ex_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

Lemma deriv_tfps_eq f g : f^`() = g^`() -> f`_0 = g`_0 -> f = g.
Proof.
move=> /deriv_tfps_ex_eq H Heq0; apply: H.
by exists 0; rewrite !horner_coef0.
Qed.

End MoreDerivative.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {tfps R n}).


Theorem deriv_exp f : (exp f)^`() = f^`()%tfps * (trXnt n.-1 (exp f)).
Proof.
case: n f => /= [| m] f.
  by rewrite [f]tfps_is_cst deriv_tfpsC mul0r expC deriv_tfpsC.
case: (boolP (f \in coef0_eq0)) => [p0_eq0 | p0_neq0]; last first.
  by rewrite exp_coef0_isnt_0 // deriv_tfps0 rmorph0 // mulr0.
rewrite !exp_coef0_eq0 //.
rewrite raddf_sum /= -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= rmorphD linearZ /=.
rewrite rmorphX tfpsX_eq0 ?coef0_eq0_trXnt // scaler0 addr0.
rewrite rmorph_sum mulr_sumr /=.
rewrite -(big_mkord predT (fun i => (i`!%:R^-1 *: f ^+ i)^`())) /=.
rewrite big_nat_recl // expr0 linearZ /= deriv_tfps1 scaler0 add0r.
apply: eq_bigr => i _.
rewrite !linearZ -scalerCA /= derivX_tfps.
rewrite -scaler_nat scalerA /= rmorphX /= -scalerAl [f^`()%tfps * _]mulrC.
congr (_ *: _).
rewrite factS natrM /= invrM ?fact_unit //.
by rewrite -mulrA [X in _ * X]mulrC divrr // mulr1.
Qed.

Theorem deriv_log f :
  f \in coef0_eq1 -> (log f)^`() = f^`()%tfps / (trXnt n.-1 f).
Proof.
case: n f => [|m] f.
  rewrite [f]tfps_is_cst coef0_eq1E coef_tfpsC => /eqP ->.
  by rewrite !deriv_tfps0p mul0r.
move => f0_eq1.
rewrite log_coef0_eq1 //.
rewrite !raddf_sum /= big_nat.
rewrite (eq_bigr (fun i => f^`()%tfps * ((1 - (trXnt m f)) ^+ i.-1))) =>
                                                  [|i /andP [hi _]]; last first.
- rewrite linearN linearZ /= derivX_tfps /=.
  rewrite -scaler_nat scalerA mulrC divrr; last by case: i hi.
  rewrite scale1r !linearD /= deriv_tfps1 add0r !linearN /=.
  by rewrite mulrN opprK trXnt1 mulrC.
- rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have tfps_unit : trXnt m f \is a GRing.unit.
    by rewrite trXn_unitE -unit_tfpsE coef0_eq1_unit.
  apply: (mulrI tfps_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  rewrite tfpsX_eq0 ?subr0 //.
  by rewrite -coef0_eq10 coef0_eq1_trXnt.
Qed.

Lemma expK : {in coef0_eq0, cancel (@exp R n) (@log R n)}.
Proof.
move => f f0_eq0 /=.
apply/eqP; rewrite -(subr_eq0 _ f); apply/eqP.
apply: (deriv_tfps_eq0 nat_unit).
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
  rewrite deriv_div_tfps; last exact: coef0_eq1_unit.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  apply/eqP; rewrite subr_eq0 [X in _ == X]mulrC.
  rewrite -eq_divr ?trXnt_unitE -?unit_tfpsE ?coef0_eq1_unit //.
  by move/(congr1 (@deriv_tfps R n)): Hlog; rewrite !deriv_log // => ->.
move/(deriv_tfps_eq0_cst nat_unit) => [c Hpq].
suff Hc : c = 1 by subst c; move: Hpq; rewrite tfpsC1; apply: divr1_eq.
move/(congr1 (fun x => x * g)): Hpq.
rewrite mulrAC -mulrA divrr ?trXnt_unitE -?unit_tfpsE ?coef0_eq1_unit //.
rewrite mulr1 -alg_tfpsC mulr_algl=> /(congr1 (fun x : {tfps R n} => x`_0)).
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


Section ExprTfps.

Variable f : {tfps R n}.
Hypothesis f0_eq1 : f \in coef0_eq1.

Let log_coef0_eq0Z c : c *: log f \in coef0_eq0.
Proof. by rewrite coef0_eq0Z // log_in_coef0_eq0. Qed.

Lemma coef0_eq1_expr c : f ^^ c \in coef0_eq1.
Proof. by rewrite /expr_tfps exp_in_coef0_eq1 log_coef0_eq0Z. Qed.

Lemma expr_tfpsn m : f ^^ m%:R = f ^+ m.
Proof.
rewrite /expr_tfps; elim: m => [|m IHm]; first by rewrite expr0 scale0r exp0.
rewrite -{1}add1n natrD scalerDl scale1r expD ?log_in_coef0_eq0 //.
by rewrite {}IHm logK // exprS.
Qed.

Lemma expr_tfps1 : f ^^ 1 = f.
Proof. by rewrite -[1]/(1%:R) expr_tfpsn expr1. Qed.

Lemma expr_tfps0 : f ^^ 0 = 1.
Proof. by rewrite -[0]/(0%:R) expr_tfpsn expr0. Qed.

Lemma expr_tfpsN a : f ^^ (- a) = (f ^^ a)^-1.
Proof. by rewrite /expr_tfps scaleNr expN. Qed.

Lemma expr_tfpsN1 : f ^^ (-1) = f ^-1.
Proof. by rewrite expr_tfpsN expr_tfps1. Qed.

Lemma expr_tfpsD a b : f ^^ (a + b) = (f ^^ a) * (f ^^ b).
Proof. by rewrite /expr_tfps scalerDl expD. Qed.

Lemma expr_tfpsB a b : f ^^ (a - b) = (f ^^ a) / (f ^^ b).
Proof. by rewrite expr_tfpsD expr_tfpsN. Qed.

Lemma expr_tfpsM a b : f ^^ (a * b) = (f ^^ a) ^^ b.
Proof. by rewrite /expr_tfps expK ?scalerA ?[b * a]mulrC. Qed.

Lemma deriv_expr_tfps a :
  (f ^^ a)^`() = a *: trXnt n.-1 (f ^^ (a - 1)) * f^`()%tfps.
Proof.
rewrite {1}/expr_tfps deriv_exp -/(f ^^ a).
rewrite linearZ /= deriv_log // -!scalerAl; congr (_ *: _).
rewrite -mulrA mulrC; congr (_ * _).
rewrite -trXntV ?leq_pred // -rmorphM ?leq_pred //= => _.
by rewrite mulrC expr_tfpsB expr_tfps1.
Qed.

End ExprTfps.

Lemma expr_tfpsNn f m : f \in coef0_eq1 -> f ^^ (-m%:R) = f ^- m.
Proof.
move=> Hf.
by rewrite -mulN1r expr_tfpsM expr_tfpsN1 ?expr_tfpsn ?exprVn ?rpredV.
Qed.

Lemma expr_tfpsK a : a \is a GRing.unit ->
  {in coef0_eq1, cancel (@expr_tfps R n a) (@expr_tfps R n a^-1)}.
Proof. by move=> aU f f0_eq1; rewrite -expr_tfpsM divrr ?expr_tfps1. Qed.

Lemma expr_tfps_inj a : a \is a GRing.unit ->
  {in coef0_eq1 &, injective (@expr_tfps R n a)}.
Proof. by move=> /expr_tfpsK/can_in_inj. Qed.


Local Notation "\sqrt f" := (f ^^ (2%:R^-1)).

Lemma sqrrK f : f \in coef0_eq1 -> \sqrt (f ^+ 2) = f.
Proof.
by move => Hh; rewrite -expr_tfpsn -?expr_tfpsM ?divrr ?expr_tfps1.
Qed.

Lemma sqrtK f : f \in coef0_eq1 -> (\sqrt f) ^+ 2 = f.
Proof.
move => Hh; rewrite -expr_tfpsn ?coef0_eq1_expr //.
by rewrite -?expr_tfpsM // mulrC divrr ?expr_tfps1.
Qed.

End DerivExpLog.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : tfps_scope.


Section CoefExpX.

Variables R : comUnitRingType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.

Lemma coef1cX n c : 1 + c *: \Xo(n) \in @coef0_eq1 R n.
Proof.
rewrite coef0_eq1E coeftD coef_tfps1.
by rewrite coeftZ coef_tfpsE val_tfpsX coefZ coefX !mulr0 addr0.
Qed.

Lemma deriv1cX n c : (1 + c *: \Xo(n.+1))^`() = c%:S :> {tfps R n}.
Proof.
rewrite linearD /= deriv_tfps1 add0r linearZ /=.
rewrite -alg_tfpsC; congr (_ *: _); apply tfps_inj.
by rewrite (val_deriv_tfps \Xo(n.+1)) val_tfpsX scale1r derivX.
Qed.

Theorem coef_expr1cX n c a m : m <= n ->
  ((1 + c *: \Xo(n)) ^^ a)`_m = c ^+ m * \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
elim: m n a => [|m IHm] n a lt_mn.
  rewrite big_ord0 /expr_tfps coef0_exp ?coef0_eq0Z ?log_in_coef0_eq0 //.
  by rewrite expr0 mul1r fact0 divr1.
case: n lt_mn => [|n] //; rewrite ltnS => le_mn.
have:= coef_deriv_tfps ((1 + c *: \Xo(n.+1)) ^^ a) m.
rewrite -mulr_natr => /(congr1 (fun x => x * m.+1%:R^-1)).
rewrite mulrK // => <-.
rewrite deriv_expr_tfps ?coef1cX // deriv1cX.
rewrite [_ * c%:S]mulrC -alg_tfpsC mulr_algl exprS coefZ.
rewrite coefZ coef_trXn le_mn {}IHm ?(leq_trans le_mn) // {n le_mn}.
rewrite mulrA factS natrM invrM // ?fact_unit // !mulrA; congr (_ * _ * _).
rewrite -[_ * a * _]mulrA [a * _]mulrC -!mulrA; congr (_ * (_ * _)).
rewrite big_ord_recl /= subr0; congr (_ * _).
by apply eq_bigr => i /= _; rewrite /bump /= natrD -[1%:R]/1 opprD addrA.
Qed.

Lemma coef_expr1X n a m :
  m <= n -> ((1 + \Xo(n)) ^^ a)`_m = \prod_(i < m) (a - i%:R) / m`!%:R :> R.
Proof.
by move=> le_mp; rewrite -[\X]scale1r coef_expr1cX // expr1n mul1r.
Qed.

End CoefExpX.


Section SquareRoot.

Variables R : idomainType.
Hypothesis nat_unit : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {tfps R n}).


Lemma sqrtE f g : f \in coef0_eq1 -> g ^+ 2 = f ->
  g = \sqrt f  \/  g = - \sqrt f.
Proof.
move=> /eqP f0_eq1 Heq.
have /eqP := (congr1 (fun f : {tfps R n} => f`_0) Heq).
rewrite -subr_eq0 {}f0_eq1 expr2 coef0_tfpsM -expr2 subr_sqr_1.
rewrite mulf_eq0 => /orP [].
- by rewrite subr_eq0 -coef0_eq1E -{}Heq {f} => Hg0; left; rewrite sqrrK.
- rewrite addr_eq0 -eqr_oppLR -coefN -raddfN -coef0_eq1E -{}Heq {f} => Hg0.
  by right; apply oppr_inj; rewrite opprK -sqrrN sqrrK.
Qed.

End SquareRoot.

End TFPSUnitRing.

Notation "\sqrt f" := (f ^^ (2%:R^-1)) : tfps_scope.


Module TFPSField.

Section TFPSField.

Variables K : fieldType.
Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma nat_unit_field i : i.+1%:R \is a @GRing.unit K.
Proof. by rewrite unitfE; move: char_K_is_zero => /charf0P ->. Qed.

Local Notation nuf := nat_unit_field.

Definition natmul_inj         := TFPSUnitRing.natmul_inj         nuf.
Definition nat_unit_alg       := TFPSUnitRing.nat_unit_alg       nuf.
Definition fact_unit          := TFPSUnitRing.fact_unit          nuf.
Definition pred_size_prim     := TFPSUnitRing.pred_size_prim     nuf.
Definition primK              := TFPSUnitRing.primK              nuf.
Definition prim_tfpsK         := TFPSUnitRing.prim_tfpsK         nuf.
Definition deriv_tfpsK        := TFPSUnitRing.deriv_tfpsK        nuf.
Definition derivXn_tfps       := TFPSUnitRing.derivXn_tfps.
Definition expD               := TFPSUnitRing.expD               nuf.
Definition expN               := TFPSUnitRing.expN               nuf.
Definition expB               := TFPSUnitRing.expB               nuf.
Definition deriv_tfps_eq0_cst := TFPSUnitRing.deriv_tfps_eq0_cst nuf.
Definition deriv_tfps_ex_eq0  := TFPSUnitRing.deriv_tfps_ex_eq0  nuf.
Definition deriv_tfps_eq0     := TFPSUnitRing.deriv_tfps_eq0     nuf.
Definition deriv_tfps_ex_eq   := TFPSUnitRing.deriv_tfps_ex_eq   nuf.
Definition deriv_tfps_eq      := TFPSUnitRing.deriv_tfps_eq      nuf.
Definition deriv_exp          := TFPSUnitRing.deriv_exp          nuf.
Definition deriv_log          := TFPSUnitRing.deriv_log          nuf.
Definition expK               := TFPSUnitRing.expK               nuf.
Definition exp_inj            := TFPSUnitRing.exp_inj            nuf.
Definition logK               := TFPSUnitRing.logK               nuf.
Definition log_inj            := TFPSUnitRing.log_inj            nuf.
Definition logM               := TFPSUnitRing.logM               nuf.
Definition logV               := TFPSUnitRing.logV               nuf.
Definition log_div            := TFPSUnitRing.log_div            nuf.
Definition coef0_eq1_expr     := TFPSUnitRing.coef0_eq1_expr.
Definition expr_tfpsn         := TFPSUnitRing.expr_tfpsn         nuf.
Definition expr_tfps0         := TFPSUnitRing.expr_tfps0         nuf.
Definition expr_tfps1         := TFPSUnitRing.expr_tfps1         nuf.
Definition expr_tfpsN         := TFPSUnitRing.expr_tfpsN         nuf.
Definition expr_tfpsN1        := TFPSUnitRing.expr_tfpsN1        nuf.
Definition expr_tfpsNn        := TFPSUnitRing.expr_tfpsNn        nuf.
Definition expr_tfpsD         := TFPSUnitRing.expr_tfpsD         nuf.
Definition expr_tfpsB         := TFPSUnitRing.expr_tfpsB         nuf.
Definition expr_tfpsM         := TFPSUnitRing.expr_tfpsM         nuf.
Definition sqrrK              := TFPSUnitRing.sqrrK              nuf.
Definition sqrtK              := TFPSUnitRing.sqrtK              nuf.
Definition coef1cX            := TFPSUnitRing.coef1cX.
Definition deriv1cX           := TFPSUnitRing.deriv1cX.
Definition coef_expr1cX       := TFPSUnitRing.coef_expr1cX       nuf.
Definition coef_expr1X        := TFPSUnitRing.coef_expr1X        nuf.
Definition sqrtE              := TFPSUnitRing.sqrtE              nuf.

End TFPSField.

End TFPSField.

Export TFPSField.
