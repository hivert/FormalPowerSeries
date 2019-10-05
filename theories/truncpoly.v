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

Delimit Scope trpoly_scope with trpoly.

Reserved Notation "{ 'trpoly' R n }"
         (at level 0, R at next level, format "{ 'trpoly'  R  n }").
Reserved Notation "[ 'trpoly' s <= n => F ]"
  (at level 0, n at next level, s ident, format "[ 'trpoly' s <= n  =>  F ]").
Reserved Notation "[ 'trpoly' s => F ]"
  (at level 0, s ident, format "[ 'trpoly'  s  =>  F ]").
Reserved Notation "c %:S" (at level 2, format "c %:S").
Reserved Notation "f *h g" (at level 2).
Reserved Notation "f ^` ()" (at level 8).



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
+ rewrite (eq_bigl (fun j => nat_of_ord j < (m - (nat_of_ord i))%N))=> [|j /=].
- rewrite big_ord_narrow => [ | _ /= ] ; first exact: leq_subr.
  by rewrite index_translation; symmetry; rewrite /G; reflexivity.
- by rewrite ltn_subRL.
+ rewrite /G (triangular_swap _ (fun i k => (nat_of_ord i) <= (nat_of_ord k))
                                (fun i k => F i (k - i)%N)).
  apply: eq_big => [ // | i _].
  rewrite (eq_bigl (fun i0 => (nat_of_ord i0) < i.+1)) => [ | j ] ; last first.
- by rewrite -ltnS.
- by rewrite big_ord_narrow.
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


Section PolyModXnTheory.

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

Lemma trXn_subproof p : size (Poly (take n.+1 p)) <= n.+1.
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

End PolyModXnTheory.

Local Open Scope trpoly_scope.

Notation "[ 'trpoly' s <= n => F ]" :=
  (trpoly_of_fun n (fun s => F)) : trpoly_scope.
Notation "[ 'trpoly' s => F ]" := [trpoly s <= _ => F] : trpoly_scope.
Notation "c %:S" := (trXn _ (c %:P)) (at level 2) : trpoly_scope.


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

Fact mul_trpoly_val f g : f * g = trXn n ((val f) * (val g)).
Proof. by []. Qed.

Fact val_mul_trpoly f g : val (f * g) = trXn n ((val f) * (val g)).
Proof. by []. Qed.

Fact exp_trpoly_val f (m : nat) : f ^+ m = trXn n ((val f) ^+ m).
Proof.
elim: m => [|m IHm]; first by rewrite !expr0 trXn1.
by rewrite exprS {}IHm /= !rmorphX /= trpolyK -exprS.
Qed.

Fact val_exp_trpoly f (m : nat) : val (f ^+ m) = trXn n ((val f) ^+ m).
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
Fact trpoly0 : trXn n (0 : {poly R}) = 0.
Proof. by rewrite linear0. Qed.

Fact trpoly1 : trXn n (1 : {poly R}) = 1.
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

End ModPolyTheory.


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
  if unit_trpoly f then [trpoly i <= n => inv_trpoly_rec f i i] else f.

Fixpoint invr_trpoly_rec f bound m :=
  if bound is b.+1 then
    if (m <= b)%N then invr_trpoly_rec f b m
    else - f`_(locked 0%N)^-1 *
           (\sum_(i < m) f`_(locked i.+1) * (invr_trpoly_rec f b (m - i.+1)%N))
  else f`_(locked 0%N)^-1.
Definition invr_trpoly f : {trpoly R n} :=
  if unit_trpoly f then [trpoly i <= n => invr_trpoly_rec f i i] else f.

Lemma coef0_inv_trpoly f : unit_trpoly f -> (inv_trpoly f)`_0 = f`_0^-1.
Proof. by rewrite /inv_trpoly => ->; rewrite coef_trpoly_of_fun /= -lock. Qed.
Lemma coef0_invr_trpoly f : unit_trpoly f -> (invr_trpoly f)`_0 = f`_0^-1.
Proof. by rewrite /invr_trpoly => ->; rewrite coef_trpoly_of_fun /= -lock. Qed.

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
Lemma coefS_invr_trpoly f m :
  unit_trpoly f -> m < n ->
  (invr_trpoly f)`_m.+1 =
  - f`_(locked 0%N)^-1 *
    (\sum_(i < m.+1) f`_(locked i.+1) * (invr_trpoly f)`_(m - i)%N).
Proof.
move=> s_unit lt_mn.
rewrite /invr_trpoly s_unit coef_trpoly_of_fun /= ltnn lt_mn; congr (- _ * _).
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

Lemma mul_trpolyrVr : {in unit_trpoly, right_inverse 1 invr_trpoly *%R}.
Proof.
move=> f s_unit; have:= s_unit; rewrite /= unfold_in => s0_unit.
apply/trpolyP => m _; elim: m {1 3 4}m (leqnn m) => [| m IHm] i.
  rewrite leqn0 => /eqP ->.
  rewrite [0%N]lock /= coef_Poly nth_take -lock //.
  rewrite coefM big_ord_recr big_ord0 sub0n [0%N]lock /=.
  by rewrite /= add0r -lock coef0_invr_trpoly // mulrV // coefC.
move=> le_im1; case: (leqP i m) => [|lt_mi]; first exact: IHm.
have {le_im1 lt_mi i} -> : i = m.+1 by apply anti_leq; rewrite le_im1 lt_mi.
rewrite coef1 [RHS]/= [m.+1]lock /= coef_Poly.
case: (ltnP m.+1 n.+1) => Hmn.
  rewrite nth_take -lock //.
  rewrite coefM big_ord_recl [m.+1]lock [val ord0]/= subn0.
  rewrite -lock coefS_invr_trpoly //.
  rewrite mulNr mulrN -lock mulVKr // addrC.
  apply/eqP; rewrite subr_eq0; apply/eqP.
  by apply eq_bigr => [] [i] /=; rewrite -lock.
by rewrite nth_default // size_take -lock (leq_trans (geq_minl _ _)).
Qed.

(* General semi-group theory : left inverse = right inverse *)
Lemma invr_trpolyE f : unit_trpoly f -> inv_trpoly f = invr_trpoly f.
Proof.
move=> H; have:= erefl (inv_trpoly f * f * invr_trpoly f).
by rewrite -{1}mulrA mul_trpolyVr // mul1r mul_trpolyrVr // mulr1.
Qed.

Lemma mul_trpolyrV : {in unit_trpoly, right_inverse 1 inv_trpoly *%R}.
Proof. by move=> f Hs; rewrite invr_trpolyE // mul_trpolyrVr. Qed.

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

Lemma unit_trpolyE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
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
rewrite invr_trpolyE // coefS_invr_trpoly // -!lock; congr (_ * _).
by apply eq_bigr => /= j _; rewrite -lock subSS.
Qed.

Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
have [f_unit|] := boolP (f \is a GRing.unit); first by rewrite coef_inv_trpoly.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite unit_trpolyE => /invr_out ->.
Qed.

Lemma trpolyC_inv (c : R) : (trXn n c%:P)^-1 = trXn n (c^-1)%:P.
Proof.
have [Uc | nUc] := boolP (c \in GRing.unit).
  by rewrite -/((trXn n \o @polyC R) _) -rmorphV.
by rewrite !invr_out // unit_trpolyE coef_trXn coefC.
Qed.

End ModPolyTheoryUnitRing.

Lemma trXnV (R : unitRingType) n m (f : {trpoly R m}) :
  n <= m -> trXn n (f^-1) = (trXn n f) ^-1.
Proof.
move=> leq_mn.
case: (boolP (f`_0 \is a GRing.unit)) => f0U; first last.
  by rewrite !invr_out // unit_trpolyE ?nth0_trXn.
apply: (@mulrI _ (trXn _ f)); rewrite ?divrr ?(unit_trpolyE, nth0_trXn) //.
rewrite -!rmorphM /= -(trXn_trXn _ leq_mn) -val_mul_trpoly.
by rewrite divrr ?unit_trpolyE // trXn1.
Qed.


Section ModPolyTheoryComUnitRing.

Variable (R : comUnitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Canonical trpoly_comUnitRingType := [comUnitRingType of {trpoly R n}].
Canonical trpoly_unitAlgType := Eval hnf in [unitAlgType R of {trpoly R n}].

(* tests *)

Lemma trXn_is_unit (p : {poly R}) :
  ((trXn n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_trpolyE nth0_trXn. Qed.

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


Section MapTrpoly.

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

(* tests *)
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


Lemma coef0_is_10 f : (f \in coef0_is_1) = ((1 - f) \in coef0_is_0).
Proof. by rewrite ?coef0_is_0E ?coef0_is_1E coefB coef1 subr_eq0 eq_sym. Qed.

Lemma coef0_is_01 f : (f \in coef0_is_0) = ((1 + f) \in coef0_is_1).
Proof. by rewrite coef0_is_10 -[RHS]rpredN !opprD !opprK addKr. Qed.

(* tests *)
Example zero_in_coef0_is_0 : 0 \in coef0_is_0.
Proof. by rewrite rpred0. Qed.

Example coef0_is_0D f g :
    f \in coef0_is_0 -> g \in coef0_is_0 -> f + g \in coef0_is_0.
Proof. by move=> hf hg; rewrite rpredD. Qed.

Example coef0_os_0N f : f \in coef0_is_0 -> (-f) \in coef0_is_0.
Proof. by move=> hf; rewrite rpredN. Qed.

Fact mulr_closed_c0_is_1 : mulr_closed coef0_is_1.
Proof.
split=> [|x y]; rewrite !coef0_is_1E ?coefC //.
by rewrite coef0_trpolyM; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.

Fact c0_is_1_key : pred_key coef0_is_1. Proof. by []. Qed.

Canonical c0_is_1_keyed := KeyedPred c0_is_1_key.
Canonical c0_is_1_MulrPred := MulrPred mulr_closed_c0_is_1.

(* tests *)
Example one_in_coef0_is_1 : 1 \in coef0_is_1.
Proof. by rewrite rpred1. Qed.

Example coef0_is_1M f g :
    f \in coef0_is_1 -> g \in coef0_is_1 -> f * g \in coef0_is_1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

End Coefficient01.
Arguments coef0_is_0 {R n}.
Arguments coef0_is_1 {R n}.

Lemma coef_trXn_is_0 (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
  (trXn m f \in coef0_is_0) = (f \in coef0_is_0).
Proof. by rewrite !coef0_is_0E nth0_trXn. Qed.

Lemma coef_trXn_is_1 (R : ringType) (n m : nat) (f : {trpoly (R) n}) :
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

Lemma divfXE (m : nat) (f : {trpoly K m}) :
  f \in (@coef0_is_0 K m) -> divfX f = trXn m.-1 (f %/ 'X).
Proof.
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

(* tests *)
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

Lemma deriv_trpolyM n (f g : {trpoly R n}) :
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
Lemma deriv_trpolyV_unit f :
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

Lemma deriv_trpolyV f :
  f \is a GRing.unit ->
  (f ^-1) ^`() = - (f ^`()%trpoly) / trXn n.-1 (f ^+ 2).
Proof.
move=> fU.
rewrite deriv_trpolyV_unit // -mulrA mulrC -mulrA !mulrN mulNr.
rewrite trXnV ?leq_pred // -invrM ?unit_trpolyE ?nth0_trXn //.
by rewrite -{1}rmorphM expr2 /= trXnE trXn_trXn ?leq_pred.
Qed.

Lemma deriv_div_trpoly f g :
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
rewrite rmorphM /= invrM ?trXn_is_unit ?nth_trXn //.
by rewrite mulrA divrr ?trXn_is_unit ?nth_trXn // mul1r.
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

Example  prim_trpolyD : {morph prim_trpoly : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma coef0_prim_trpoly f : (prim_trpoly f)`_0 = 0.
Proof. by rewrite coef_poly eqxx mulr0n invr0 mulr0. Qed.

End Primitive.


Section Composition.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition comp_trpoly m (g p : {trpoly R m}) :=
  if g \in coef0_is_0 then trXn m (comp_poly g p) else 0.

Local Notation "f \So g" := (comp_trpoly g f) (at level 2) : trpoly_scope.

Lemma comp_trpoly_coef0_neq0 f g :
  g \notin coef0_is_0 -> f \So g = 0.
Proof. by move/negbTE => p0_neq0; rewrite /comp_trpoly p0_neq0. Qed.

Lemma comp_trpoly_coef0_eq0 f g :
  g \in coef0_is_0 -> f \So g = trXn n (comp_poly g f).
Proof. by move => f0_eq0 ; rewrite /comp_trpoly f0_eq0. Qed.

Section Variable_f.

Variable (f : {trpoly R n}).

Lemma comp_trpoly0r : f \So 0 = (f`_0) %:S.
Proof. by rewrite comp_trpoly_coef0_eq0 ?rpred0 // comp_poly0r. Qed.

Lemma comp_trpolyr0 : 0 \So f = 0.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in coef0_is_0).
+ by rewrite comp_trpoly_coef0_eq0 // comp_poly0 rmorph0.
+ by rewrite comp_trpoly_coef0_neq0.
Qed.

(* is there a better statement ? *)
Lemma comp_trpolyC (c : R) :
  c%:S \So f = (c * (f \in coef0_is_0)%:R) %:S.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in coef0_is_0).
+ rewrite comp_trpoly_coef0_eq0 //=; have /= -> := trXnC n c.
  by rewrite comp_polyC mulr1.
+ by rewrite mulr0 trXn0 comp_trpoly_coef0_neq0.
Qed.

Lemma comp_trpolyCf (c : R) : f \So (c%:S) = (f`_0 * (c == 0)%:R) %:S.
Proof.
have [->| /negbTE c_neq0] := eqVneq c 0.
  by rewrite eqxx mulr1 rmorph0 comp_trpoly0r.
rewrite comp_trpoly_coef0_neq0; last first.
  by rewrite coef0_is_0E nth0_trXn coefC eqxx negbT.
by rewrite c_neq0 mulr0 rmorph0.
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
End Composition.


Section MoreComposition.

Variables (R : comRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Local Notation "f \So g" := (comp_trpoly g f) (at level 2) : trpoly_scope.

Lemma deriv_trpoly_comp f g :
  f \in coef0_is_0 ->
  deriv_trpoly (g \So f) = (g ^`()%trpoly \So (trXn n.-1 f)) * f^`()%trpoly.
Proof.
rewrite !deriv_trpolyE //.
move: f g; case: n => [|m] f g f0_eq0.
  rewrite [f]trpoly_is_cst [g]trpoly_is_cst !trXn_trXn // comp_trpolyC.
  by rewrite !val_trpolyC !derivC trXn0 mulr0.
rewrite /= comp_trpoly_coef0_eq0 // comp_trpoly_coef0_eq0 ?p0_is_0; last first.
  by rewrite coef0_is_0E nth0_trXn -coef0_is_0E.
apply/val_inj.
rewrite deriv_trXn deriv_comp trXn_trXn //= !trXnE trXn_mulr -trXn_mull.
congr (val (trXn _ (_ * _))).
rewrite -val_deriv_trpoly trpolyK.
rewrite !comp_polyE !linear_sum /= !linear_sum; apply: eq_bigr => [] [i /=] _ _.
rewrite !trXnE !linearZ /=; congr (_ *: _).
by rewrite !trXnE !rmorphX /= trXnE trXn_trXn.
Qed.

End MoreComposition.

Fact coeffX_eq0 (R : ringType) n m (p : {poly R}) :
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

Fact trXn_eq0 (R : ringType) n m (p : {poly R}) :
  p`_0 = 0 -> n < m -> trXn n (p ^+ m) = 0.
Proof.
move=> H1 H2.
apply/trpolyP => i le_in; rewrite coef_trXn coef0 le_in.
by rewrite coeffX_eq0 // (leq_ltn_trans le_in H2).
Qed.

Lemma expr_coef0_is_0 (R : ringType) (n m : nat) :
  n < m -> {in coef0_is_0, forall f : {trpoly R n}, f ^+ m = 0}.
Proof.
move => lt_mn f; rewrite coef0_is_0E; move/eqP.
move/trXn_eq0/(_ lt_mn) => <-.
by rewrite rmorphX /= trpolyK.
Qed.


Section ExpLog.

Variables (R : unitRingType) (n : nat).
Implicit Types (f g : {trpoly R n}).

Definition exp f : {trpoly R n} :=
  if f \notin coef0_is_0 then 0 else
  trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (val f ^+i)).

Definition log f : {trpoly R n} :=
  if f \notin coef0_is_1 then 0 else
  trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - val f) ^+i)).


Lemma exp_coef0_is_0 f : f \in coef0_is_0 ->
  exp f = trXn n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: ((val f) ^+i)).
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_is_0 -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0 : exp (0 : {trpoly R n}) = 1.
Proof.
apply/trpolyP => i le_in.
rewrite exp_coef0_is_0 ?rpred0 // rmorph_sum /=.
rewrite big_ord_recl /= fact0 expr0n eq_refl /= invr1 scale1r trXnE trXn1.
rewrite coefD /= big1 ?coef0 ?addr0 // => [] [j ] _ _ /=.
by rewrite /bump /= add1n expr0n /= scaler0 trXn0.
Qed.

Lemma expC (c : R) : exp (c %:S) = (c == 0)%:R %:S :> {trpoly R n}.
Proof.
have [| p0N0] := boolP (c %:S \in @coef0_is_0 R n).
+ rewrite coef0_is_0E nth0_trXn coefC /= => /eqP ->.
  by rewrite eq_refl trpolyC0 trpolyC1 exp0.
+ rewrite exp_coef0_isnt_0 //.
  move: p0N0; rewrite coef0_is_0E nth0_trXn coefC /= => /negbTE ->.
  by rewrite rmorph0.
Qed.

Lemma log_coef0_is_1 f : f \in coef0_is_1 ->
  log f = trXn n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - (val f)) ^+i)).
Proof. by rewrite /log => ->. Qed.

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


Section DerivComRing.

Variables (R : comRingType) (n : nat).
Implicit Type f : {trpoly R n}.

Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Lemma deriv_trpolyX f m : (f ^+ m)^` () = f^`() * (trXn n.-1 f) ^+ m.-1 *+ m.
Proof.
elim: m => /= [|m IHm]; first by rewrite expr0 mulr0n -trpolyC1 deriv_trpolyC.
rewrite exprS deriv_trpolyM {}IHm (mulrC (_ f)) val_exp_trpoly /=.
rewrite mulrC -mulrnAr mulrCA -mulrDr -mulrnAr; congr (_ * _).
rewrite trXnE trXn_trXn ?leq_pred //.
rewrite rmorphX /= mulrnAr -exprS; case: m => /= [|m]; rewrite -?mulrS //.
by rewrite !expr0 mulr0n addr0.
Qed.

End DerivComRing.


Section ExpLogComUnitRing.

Variables (R : comUnitRingType) (n : nat).
Implicit Type f : {trpoly R n}.

(* is there a better statement ? something like: *)
(* Lemma coef0_exp f : (exp f)`_0 = (f \notin coef0_is_0)%:R. *)
Lemma coef0_exp f : f \in coef0_is_0 -> (exp f)`_0 = 1.
Proof.
move => f0_eq0.
rewrite exp_coef0_is_0 // coef_trXn leq0n -horner_coef0.
rewrite -horner_evalE rmorph_sum /=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == 0%N)%:R)) => [ | [i _] _ ] /=.
+ rewrite -(big_mkord predT (fun i => ((i == _)%:R))) big_ltn ?ltnS //.
  rewrite eqxx /= -natr_sum big_nat_cond.
  rewrite (eq_big (fun i => (0 < i < n.+1)) (fun i => 0%N)) => [ | i | i ].
- by rewrite big1_eq addr0.
- by rewrite andbT.
  by rewrite andbT => /andP [/lt0n_neq0/negbTE -> _].
+ rewrite linearZ /= rmorphX /= horner_evalE horner_coef0.
  move: f0_eq0 ; rewrite coef0_is_0E => /eqP ->.
  rewrite expr0n ; case: i => [ | i'].
- by rewrite fact0 invr1 mul1r.
- by rewrite eqn0Ngt -leqNgt ltn0 mulr0.
Qed.

Lemma coef0_log (f : {trpoly R n}) : (log f)`_0 = 0.
Proof.
have [f0_eq1|f0_neq1] := boolP (f \in coef0_is_1); last first.
  by rewrite log_coef0_isnt_1 // coefC.
rewrite log_coef0_is_1 // coef_trXn leq0n -horner_coef0.
rewrite -horner_evalE rmorphN rmorph_sum /=.
rewrite big_nat_cond (eq_bigr (fun i => (i == 0%N)%:R)).
+ rewrite -[1%N]add0n big_addn (eq_bigr (fun i => 0)) => [ | i _]; last first.
    by rewrite addn1.
  by rewrite big1_eq oppr0.
+ move => i /andP [/andP [Hi _] _] /=.
  rewrite linearZ rmorphX rmorphB /= !horner_evalE hornerC horner_coef0.
  move: f0_eq1 ; rewrite coef0_is_1E => /eqP ->.
  by rewrite subrr expr0n eqn0Ngt Hi /= mulr0.
Qed.

End ExpLogComUnitRing.



Module TrpolyUnitRing.

Section PrimitiveUnitRing.

Variable R : unitRingType.
Hypothesis nat_inv : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

(* Is this useful ? *)
Fact natmul_inj (m : nat) : (m%:R == 0 :> R) = (m == 0%N).
Proof.
case: m => [|m]; first by rewrite eq_refl; apply/eqP.
rewrite {2}/eq_op /=.
apply/negP => /eqP/(congr1 (fun x => x \is a GRing.unit)).
by rewrite nat_inv unitr0.
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
Hypothesis nat_inv : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.

Implicit Types (f g : {trpoly R n}).


Lemma fact_unit m : m`!%:R \is a @GRing.unit R.
Proof. by have:= fact_gt0 m; rewrite lt0n; case: m`!. Qed.

Lemma exp_is_morphism :
  {in (@coef0_is_0 R n) &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move=> f g f0_eq0 g0_eq0 /=.
rewrite ?(exp_coef0_is_0, rpredD) //.
apply/val_inj => /=; apply/val_inj => /=.
rewrite !trXnE trXn_mul.
rewrite !coef0_is_0E -!horner_coef0 in f0_eq0 g0_eq0.
move/eqP: g0_eq0 ; move/eqP : f0_eq0.
move: f g => [f fr] [g gr] /=.
rewrite !horner_coef0 => f0_eq0 g0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *:
         (\sum_(j < i'.+1) f ^+ (i' - j) * g ^+ j *+ 'C(i', j)))); last first.
  by move => i _ /=; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i' .+1)
        ((j`! * (i' -j)`!)%:R) ^-1 *: (f ^+ (i' - j) * g ^+ j)))); last first.
  move => [i i_lt_Sn] _ /=.
  rewrite scaler_sumr; apply: eq_bigr => [ /= [j j_lt_Si]] _ /=.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl; congr(_ *: _).
  case: i i_lt_Sn j_lt_Si => [|i] _.
    by rewrite ltnS leqn0 => /eqP ->; rewrite fact0 bin0 mulr1 muln1.
  rewrite ltnS => Hi; rewrite bin_factd //.
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
          trXn n (\sum_(i < n.+1) \sum_(j < n.+1 | i+j <= n)
                   (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)).
  rewrite !rmorph_sum; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !rmorph_sum.
  rewrite (bigID (fun j => i + (nat_of_ord j) <= n)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= n))
                      (fun j => trXn n ((i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)))).
  apply: big1_seq => /= j.
  rewrite -ltnNge; move/andP => [ n_lt_addij _]; rewrite linearZ /=.
  suff -> : trXn n (f ^+ i * g ^+ j) = 0 by rewrite scaler0.
  apply/trpolyP => l le_li; rewrite coef0.
  rewrite coef_trXn le_li coefM.
  rewrite (bigID (fun k => val k >= i)) /= ?big1 ?addr0 // => [] [k Hk] /= H.
  - rewrite -ltnNge in H.
    by rewrite coeffX_eq0 ?mul0r.
  - rewrite ltnS in Hk.
    rewrite [X in _* X]coeffX_eq0 ?mulr0 //.
    rewrite leq_ltn_subLR //.
    exact: (leq_ltn_trans le_li (leq_trans n_lt_addij (leq_add _ _))).
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

Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Lemma deriv_trpoly0_cst f : f^`() = 0 -> {c : R | f = c %:S}.
Proof.
move: f; case: n => [f _| m f]; first by rewrite [f]trpoly_is_cst; exists (f`_0).
move=> H; exists (f`_0).
apply/trpolyP => [] [|i]; rewrite coef_trpolyC // ltnS [RHS]/= => le_im.
apply: (mulIr (nat_inv i)); rewrite mul0r.
move: H => /(congr1 (fun x : {trpoly _ _ } => x`_i)).
by rewrite coef_deriv_trpoly coef0 -mulr_natr.
Qed.

Lemma deriv_trpoly0_eq0 f :
  f^`() = 0 -> {x : R | (val f).[x] = 0} -> f = 0.
Proof.
move=> /deriv_trpoly0_cst [c ->] [x].
rewrite val_trpolyC /= hornerC => ->.
by rewrite trpolyC0.
Qed.

Lemma deriv_trpoly0_eq f g :
  f ^` () = g ^` () -> {x : R | (val f).[x] = (val g).[x]} -> f = g.
Proof.
move=> H [x Hx].
apply/eqP; rewrite -(subr_eq0 f g); apply/eqP.
apply: deriv_trpoly0_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

End ExpLogMorph.


Section DerivExpLog.

Variables R : comUnitRingType.
Hypothesis nat_inv : forall i, i.+1%:R \is a @GRing.unit R.
Variable n : nat.
Implicit Types (f g : {trpoly R n}).

Local Notation "f ^` ()" := (deriv_trpoly f) (at level 8) : ring_scope.

Lemma deriv_exp f : (exp f)^` () = f^` () * (trXn n.-1 (exp f)).
Proof.
move: f; case: n => /= [| m] f.
  by rewrite [f]trpoly_is_cst deriv_trpolyC mul0r expC deriv_trpolyC.
have [p0_eq0 | p0_neq0] := boolP (f \in coef0_is_0); last first.
  by rewrite exp_coef0_isnt_0 // deriv_trpoly0 rmorph0 mulr0.
rewrite !exp_coef0_is_0 //= !deriv_trpolyE //=; apply/val_inj => /=.
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

Lemma deriv_log f :
  f \in coef0_is_1 -> (log f) ^` () = (f )^` () / (trXn n.-1 f).
Proof.
case: n f => [|m] f.
  rewrite [f]trpoly_is_cst coef0_is_1E nth0_trXn coefC eqxx => /eqP ->.
  by rewrite !deriv_trpoly0p mul0r.
move => f0_is_1.
rewrite log_coef0_is_1 // rmorphN rmorph_sum linearN raddf_sum -sumrN.
rewrite big_nat.
rewrite (eq_bigr (fun i => (f )^` () * ((1 - (trXn m f)) ^+ i.-1))) =>
                                                  [|i /andP [hi _]]; last first.
- rewrite linearZ rmorphX /= deriv_trpolyZ rmorphB rmorph1 /= deriv_trpolyX.
  rewrite linearB rmorphB rmorph1 -trpolyC1 /= deriv_trpolyC sub0r /= trXn_trXn //.
  rewrite -scaler_nat scalerA mulrC divrr; last by case: i hi.
  by rewrite scale1r mulNr opprK trpolyK.
+ rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : trXn m f \is a GRing.unit.
    rewrite trXn_is_unit.
    move: f0_is_1 ; rewrite coef0_is_1E => /eqP ->.
    exact: unitr1.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  rewrite expr_coef0_is_0 ?subr0 //.
  by rewrite -coef0_is_10 coef_trXn_is_1.
Qed.

Lemma cancel_log_exp : {in coef0_is_0, cancel (@exp R n) (@log R n)}.
Proof.
move => f f0_eq0 /=.
apply/eqP; rewrite -(subr_eq0 _ f); apply/eqP.
apply: (deriv_trpoly0_eq0 nat_inv).
- rewrite linearB /= deriv_log ?coef0_is_1E ?coef0_exp //.
  rewrite deriv_exp // -mulrA divrr ?mulr1 ?subrr // trXn_is_unit.
  by rewrite coef0_exp // unitr1.
- exists 0; rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0.
  by rewrite coef0_log sub0r; apply/eqP; rewrite oppr_eq0 -coef0_is_0E.
Qed.

Lemma exp_inj : {in coef0_is_0 &, injective (@exp R n)}.
Proof. exact: (can_in_inj cancel_log_exp). Qed.

Lemma log_inj : {in coef0_is_1 &, injective (@log R n)}.
Proof.
move=> p q p0_eq0 q0_eq0 /= Hlog.
have {Hlog} : (p/q) ^` () = 0.
  rewrite deriv_div_trpoly; last first.
    by move: q0_eq0; rewrite coef0_is_1E unit_trpolyE => /eqP ->; apply unitr1.
  rewrite [X in X / _](_ : _ = 0) ?mul0r //.
  apply/eqP; rewrite subr_eq0 [trXn n.-1 p * q^`()%trpoly]mulrC.
  rewrite -eq_divr ?trXn_is_unit ; last 2 first.
    by move: p0_eq0; rewrite coef0_is_1E => /eqP ->; apply unitr1.
    by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply unitr1.
  by move/(congr1 (@deriv_trpoly R n)): Hlog; rewrite !deriv_log // => ->.
move/(deriv_trpoly0_cst nat_inv) => [c Hpq].
suff Hc : c = 1 by subst c; move: Hpq; rewrite trpolyC1; apply: divr1_eq.
move/(congr1 (fun x => x * q)): Hpq.
rewrite mulrAC -mulrA divrr; last first.
  rewrite unit_trpolyE.
  by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply unitr1.
rewrite mulr1.
rewrite -alg_trpolyC mulr_algl.
move/(congr1 (fun x : {trpoly (R) n} => x`_0)).
rewrite coefZ.
move: p0_eq0; rewrite coef0_is_1E => /eqP ->.
move: q0_eq0; rewrite coef0_is_1E => /eqP ->.
by rewrite mulr1 => ->.
Qed.

Lemma cancel_exp_log : {in coef0_is_1 , cancel (@log R n) (@exp R n)}.
Proof.
move=> p p0_eq1 /=.
apply: log_inj => //.
  rewrite coef0_is_1E.
  apply/eqP; rewrite coef0_exp //.
  by rewrite coef0_is_0E; apply/eqP; rewrite coef0_log.
by rewrite cancel_log_exp // coef0_is_0E coef0_log.
Qed.

Lemma log_is_morphism :
  {in (@coef0_is_1 R n) &, {morph log : f g / f * g >-> f + g}}.
Proof.
move=> f g f0_eq1 g0_eq1 /=.
apply exp_inj; rewrite ?coef0_is_0E ?coefD ?coef0_log ?addr0 //.
rewrite exp_is_morphism // ?coef0_is_0E ?coef0_log //.
rewrite !cancel_exp_log // coef0_is_1E coef0_trpolyM.
move: f0_eq1 g0_eq1; rewrite !coef0_is_1E => /eqP -> /eqP ->.
by rewrite mulr1.
Qed.

End DerivExpLog.

End TrpolyUnitRing.


Module TrpolyField.

Section TrpolyField.

Variables K : fieldType.
Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma nat_inv_field i : i.+1%:R \is a @GRing.unit K.
Proof. by rewrite unitfE; move: char_K_is_zero => /charf0P ->. Qed.

Notation nif := nat_inv_field.

Definition pred_size_prim    := TrpolyUnitRing.pred_size_prim nif.
Definition primK             := TrpolyUnitRing.primK nif.
Definition prim_trpolyK      := TrpolyUnitRing.prim_trpolyK nif.
Definition deriv_trpolyK     := TrpolyUnitRing.deriv_trpolyK nif.
Definition exp_is_morphism   := TrpolyUnitRing.exp_is_morphism nif.
Definition deriv_trpoly0_cst := TrpolyUnitRing.deriv_trpoly0_cst nif.
Definition deriv_trpoly0_eq0 := TrpolyUnitRing.deriv_trpoly0_eq0 nif.
Definition deriv_trpoly0_eq  := TrpolyUnitRing.deriv_trpoly0_eq nif.
Definition deriv_exp         := TrpolyUnitRing.deriv_exp nif.
Definition deriv_log         := TrpolyUnitRing.deriv_log nif.
Definition cancel_log_exp    := TrpolyUnitRing.cancel_log_exp nif.
Definition log_inj           := TrpolyUnitRing.log_inj nif.
Definition cancel_exp_log    := TrpolyUnitRing.cancel_exp_log nif.
Definition log_is_morphism   := TrpolyUnitRing.log_is_morphism nif.

End TrpolyField.

End TrpolyField.

Import TrpolyField.
