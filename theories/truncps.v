(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple finfun bigop finset fingroup.
From mathcomp Require Import perm ssralg poly polydiv mxpoly binomial bigop.
From mathcomp Require Import finalg zmodp matrix mxalgebra polyXY ring_quotient.

Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing.Theory.
Local Open Scope ring_scope.
(* Local Open Scope quotient_scope. *)

Delimit Scope tfps_scope with tfps.

Reserved Notation "{ 'tfps' K n }"
         (at level 0, K at next level, format "{ 'tfps'  K  n }").
Reserved Notation "[ 'tfps' s <= n => F ]"
  (at level 0, n at next level, s ident, format "[ 'tfps' s <= n  =>  F ]").
Reserved Notation "[ 'tfps' s => F ]"
  (at level 0, s ident, format "[ 'tfps'  s  =>  F ]").
Reserved Notation "c %:S" (at level 2).
Reserved Notation "f *h g" (at level 2).
Reserved Notation "f ^` ()" (at level 8).

Local Notation "p ^ f" := (map_poly f p).


Lemma poly_cat (R : ringType) (p : {poly R}) n :
  p = Poly (take n p) + 'X^n * Poly (drop n p).
Proof.
apply/polyP=> i; rewrite coefD coefXnM !coef_Poly; case: ltnP => Hi.
by rewrite nth_take // addr0.
rewrite nth_drop subnKC // [(take _ _)`_i]nth_default ?add0r //.
by rewrite size_take -/(minn _ _) (leq_trans (geq_minl _ _) Hi).
Qed.

Lemma leadX_unit (R : unitRingType) :
  lead_coef (R := R) 'X \is a GRing.unit.
Proof. by rewrite lead_coefX unitr1. Qed.
Hint Resolve leadX_unit.
Lemma leadXn_unit (R : unitRingType) n :
  lead_coef (R := R) 'X^n \is a GRing.unit.
Proof. by rewrite lead_coefXn unitr1. Qed.
Hint Resolve leadXn_unit.

Lemma leadX_unit_id (R : idomainType) :
  lead_coef (R := R) 'X \is a GRing.unit.
Proof. exact: leadX_unit. Qed.
Hint Resolve leadX_unit_id.
Lemma leadXn_unit_id (R : idomainType) n :
  lead_coef (R := R) 'X^n \is a GRing.unit.
Proof. exact: leadXn_unit. Qed.
Hint Resolve leadXn_unit_id.


Section MorePolyTheory.

Variable (R : ringType).

Lemma leq_size_deriv (p : {poly R}) : size p^`() <= (size p).-1.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
by rewrite -ltnS prednK // ?lt_size_deriv // size_poly_gt0.
Qed.

Lemma p_neq0 (p : {poly R}): (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
by move => [x px_neq0]; move: px_neq0; apply: contra => /eqP ->; rewrite horner0.
Qed.

Variable (K : idomainType).

Lemma poly_modXn (p : {poly K}) n : p %% 'X^n = Poly (take n p).
Proof.
rewrite {1}(poly_cat p n) addrC mulrC Pdiv.IdomainUnit.modp_addl_mul_small //.
rewrite size_polyXn ltnS (leq_trans (size_Poly _)) //.
by rewrite size_take -/(minn _ _) geq_minl.
Qed.

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

(* this kind of injectivity + deriv result could be useful ? *)
(* Lemma deriv_poly_eq (K : fieldType) (p q : {poly K}) :
    p`_0 == q`_0 -> p^`() == q^`() -> p = q.
Proof.
rewrite -subr_eq0 -coefB -[p^`() == q^`()]subr_eq0 -derivB.
move => coef0_eq0 deriv_eq0 ; apply/eqP.
rewrite -subr_eq0 ; apply/eqP ; move: coef0_eq0 deriv_eq0.
exact: deriv_poly_eq0.
Qed. *)

End MorePolyTheory.

Section ModPolyTheory.

Variable (K : idomainType).

Fact leq_modpXn m (p : {poly K}) : size (p %% 'X^m) <= m.
Proof.
by rewrite -ltnS (leq_trans (ltn_modpN0 _ _)) // -?size_poly_eq0 size_polyXn.
Qed.

Lemma coef_modXn m (p : {poly K}) i : (p %% 'X^m)`_i =
  if i < m then p`_i else 0.
Proof.
have [lt_i_m|le_m_i] := ltnP; last first.
  by rewrite nth_default // (leq_trans (leq_modpXn _ _)).
rewrite {2}(Pdiv.IdomainMonic.divp_eq (monicXn K m) p).
by rewrite coefD !coefMXn lt_i_m add0r.
Qed.

(* should not be visible outside this file *)
Fact modCXn a n : 0 < n -> a%:P %% 'X^n = a%:P :> {poly K}.
Proof.
move=> lt_0n.
by rewrite modp_small // size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
Qed.

Fact modp_modp (p u v : {poly K}) :
  u \is monic -> v \is monic -> u %| v -> (p %% v) %% u = p %% u.
Proof.
move => mu mv /(Pdiv.IdomainMonic.dvdpP mu) => /= [[qq Hv]].
have leadv : lead_coef v \is a GRing.unit.
  by move/monicP: mv => ->; apply: unitr1.
have leadu : lead_coef u \is a GRing.unit.
  by move/monicP: mu => ->; apply: unitr1.
rewrite (Pdiv.IdomainMonic.divp_eq mv p) !Pdiv.IdomainUnit.modp_add //.
rewrite !modp_mod Pdiv.Idomain.modp_mull mod0p add0r.
by rewrite {3}Hv mulrA Pdiv.Idomain.modp_mull add0r.
Qed.

Fact coef0M (p q : {poly K}) : (p * q)`_0 = p`_0 * q`_0.
(* Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed. *)
Proof. by rewrite -!horner_coef0 hornerM. Qed.

(* should not be visible outside this file *)
Fact modX_eq0 (p : {poly K}) (n m : nat) : p`_0 = 0 -> n < m ->
  (p ^+ m) %% 'X^n.+1 = 0.
Proof.
rewrite -horner_coef0 => /polyXsubCP p0_eq0 n_lt_m.
rewrite polyC0 subr0 in p0_eq0.
apply/modp_eq0P.
by rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_m)) // dvdp_exp2r.
Qed.

End ModPolyTheory.

Section MoreBigop.

Definition swap (R : Type) (x : R * R) := (x.2, x.1).

Lemma swap_inj (R : Type) : involutive (@swap R).
Proof. by move => [x1 x2]. Qed.

Lemma triangular_swap (R : Type) (idx : R) (op : Monoid.com_law idx)
                 (m : nat) (P : 'I_m -> 'I_m -> bool) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | P i j) F i j =
  \big[op/idx]_(j < m) \big[op/idx]_(i < m | P i j) F i j.
Proof. by rewrite !pair_big_dep (reindex_inj (inv_inj (@swap_inj _))). Qed.

Lemma index_translation (R : Type) (idx : R) (op : Monoid.law idx)
                                                     (m j : nat) (F : nat -> R) :
  \big[op/idx]_(i < m - j) F i =
  \big[op/idx]_(k < m | j <= k)  F (k - j)%N.
Proof.
rewrite -(big_mkord predT F) /= (big_mknat _ j m (fun k => F (k - j)%N)).
rewrite -{2}[j]add0n (big_addn 0 m j _ _).
by apply: eq_bigr => i _ ; rewrite addnK.
Qed.

Lemma aux_triangular_index_bigop (R : Type) (idx : R) (op : Monoid.com_law idx)
                                                (m : nat) (F : nat -> nat -> R) :
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

Lemma triangular_index_bigop (R : Type) (idx : R) (op : Monoid.com_law idx)
                             (m n: nat) (F : nat -> nat -> R) :
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

Section TruncatedPowerSeries.

Variables (K : idomainType) (n : nat).

Record tfps := MkTfps
{
  truncated_tfps :> {poly K};
  _ : size truncated_tfps <= n.+1
}.

Definition tfps_of of phant K := tfps.
Local Notation "'{tfps}'" := (tfps_of (Phant K)).

Canonical tfps_subType := [subType for truncated_tfps].
Definition tfps_eqMixin := [eqMixin of tfps by <:].
Canonical tfps_eqType := EqType {tfps} tfps_eqMixin.
Definition tfps_choiceMixin := [choiceMixin of tfps by <:].
Canonical tfps_choiceType := ChoiceType {tfps} tfps_choiceMixin.

Definition Tfps_of (p : {poly K}) (p_small : size p <= n.+1) :
    {tfps} := MkTfps p_small.

Definition Tfpsp (p : {poly K}) := Tfps_of (leq_modpXn _ p).

Definition tfps_of_fun (f : nat -> K) := Tfps_of (size_poly _ f).

End TruncatedPowerSeries.

Section TruncatedPowerSeriesTheory.

Variables (K : idomainType) (n : nat).

Local Notation "{ 'tfps' K n }" := (tfps_of n (Phant K)).
Local Notation tfps := {tfps K n}.
Local Notation "[ 'tfps' s <= n => F ]" := (tfps_of_fun n (fun s => F)).
Local Notation "[ 'tfps' s => F ]" := [tfps s <= n => F].

Implicit Types (f g : tfps).

Lemma size_tfps f : size (val f) <= n.+1.
Proof. by case: f. Qed.

Fact mod_tfps (m : nat) f : n <= m -> f %% 'X^m.+1 = (val f).
Proof.
move => leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_tfps _)).
Qed.

Fact Tfpsp_modp (m : nat) (p : {poly K}) : n < m ->
  Tfpsp n (p %% 'X^m) = Tfpsp n p.
Proof.
by move=> lt_nm; apply/val_inj=> /=; rewrite modp_modp // ?dvdp_exp2l ?monicXn //.
Qed.

Lemma tfps_nth_default f j : j > n ->  f`_j = 0.
Proof. by move=> j_big; rewrite nth_default // (leq_trans _ j_big) ?size_tfps. Qed.

Lemma tfps_coefK f : [tfps s => f`_s] = f.
Proof.
apply/val_inj/polyP=> j; rewrite coef_poly ltnS.
by have  [//|j_big] := leqP; rewrite tfps_nth_default.
Qed.

Lemma coef_tfps s (f : nat -> K) :
  [tfps s => f s]`_s = if s <= n then f s else 0.
Proof. by rewrite coef_poly. Qed.

Lemma eq_tfps f g : (forall i : 'I_n.+1, f`_i = g`_i) <-> (f = g).
Proof.
split=> [eq_s|-> //]; apply/val_inj/polyP => i /=.
have [i_small|i_big] := ltnP i n.+1; first by rewrite (eq_s (Ordinal i_small)).
by rewrite -[f]tfps_coefK -[g]tfps_coefK !coef_tfps leqNgt i_big.
Qed.

Lemma nth0_Tfpsp (p : {poly K}) : (Tfpsp n p)`_0 = p`_0.
Proof. by rewrite coef_modXn ltn0Sn. Qed.

(* zmodType structure *)

Fact zero_tfps_subproof : size (0 : {poly K}) <= n.+1.
Proof. by rewrite size_poly0. Qed.

Definition zero_tfps := Tfps_of zero_tfps_subproof.

Lemma add_tfps_subproof f g :
  size (val f + val g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_tfps. Qed.

Definition add_tfps f g := Tfps_of (add_tfps_subproof f g).

Lemma opp_tfps_proof f : size (- val f) <= n.+1.
Proof. by rewrite size_opp ?size_tfps. Qed.

Definition opp_tfps f := Tfps_of (opp_tfps_proof f).

Fact add_tfpsA : associative add_tfps.
Proof. by move => f1 f2 f3; apply/val_inj; apply: addrA. Qed.

Fact add_tfpsC : commutative add_tfps.
Proof. by move => f1 f2; apply/val_inj; apply: addrC. Qed.

Fact add_tfps0f : left_id zero_tfps add_tfps.
Proof. by move => f; apply/val_inj; apply: add0r. Qed.

Fact add_tfpsK : left_inverse zero_tfps opp_tfps add_tfps.
Proof. by move => f; apply/val_inj; apply: addNr. Qed.

Definition tfps_zmodMixin :=
                              ZmodMixin add_tfpsA add_tfpsC add_tfps0f add_tfpsK.
Canonical tfps_zmodType := ZmodType tfps tfps_zmodMixin.

Lemma Tfpsp0 : Tfpsp n 0 = 0.
Proof. by apply/val_inj => /=; rewrite mod0p. Qed.

(* ringType structure *)

Fact one_tfps_proof : size (1 : {poly K}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.

Definition one_tfps : tfps := Tfps_of one_tfps_proof.

Definition mul_tfps f g := Tfpsp n (val f * val g).

Definition hmul_tfps f g := [tfps j => f`_j * g`_j].

Definition deriv_tfps f : {tfps K n.-1} := [tfps s <= n.-1 => f`_s.+1 *+ s.+1].

Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsC : commutative hmul_tfps.
Proof.
by move=> f1 f2; apply/val_inj/polyP => /= i; rewrite !coef_poly mulrC.
Qed.

Lemma hmul_tfpsA : associative hmul_tfps.
Proof.
move=> f1 f2 f3; apply/val_inj/polyP => /= i.
by rewrite // !coef_poly; case: (_ < _) => //; apply: mulrA.
Qed.

Lemma hmul_tfps0r f : 0 *h f = 0.
Proof.
by apply/val_inj/polyP=> i /=; rewrite coef_poly coef0 mul0r if_same.
Qed.

Lemma hmul_tfpsr0 f : f *h 0 = 0.
Proof. by rewrite hmul_tfpsC hmul_tfps0r. Qed.

Fact left_id_one_mul_tfps : left_id one_tfps mul_tfps.
Proof.
move=> p; apply val_inj; rewrite /= mul1r.
by rewrite modp_small // size_polyXn ltnS ?size_tfps.
Qed.

Fact mul_tfpsC : commutative mul_tfps.
Proof. by move=> f1 f2; apply val_inj => /=; rewrite mulrC. Qed.

Fact left_distributive_mul_tfps : left_distributive mul_tfps add_tfps.
Proof.
move=> f1 f2 f3; apply val_inj => /=; rewrite mulrDl.
by rewrite Pdiv.IdomainUnit.modp_add.
Qed.

Fact mul_tfpsA : associative mul_tfps.
Proof.
move=> f1 f2 f3; apply/val_inj.
by rewrite /= [in RHS]mulrC !Pdiv.IdomainUnit.modp_mul // mulrA mulrC.
Qed.

Fact one_tfps_not_zero : one_tfps != 0.
Proof. by rewrite -val_eqE oner_neq0. Qed.

Definition tfps_ringMixin := ComRingMixin mul_tfpsA mul_tfpsC
               left_id_one_mul_tfps left_distributive_mul_tfps one_tfps_not_zero.

Canonical tfps_ringType := RingType tfps tfps_ringMixin.
Canonical tfps_comRingType := ComRingType tfps mul_tfpsC.

(* comUnitRingType structure *)

Lemma coef_Tfpsp (p : {poly K}) s : (Tfpsp n p)`_s = if s <= n then p`_s else 0.
Proof. by rewrite coef_modXn. Qed.

Fixpoint coef_inv_rec (p : {poly K}) (m i : nat) : K :=
  match m with
    | O => p`_(locked 0%N) ^-1
    | S m => if i == 0%N then p`_(locked 0%N) ^-1
             else - p`_(locked 0%N) ^-1 * \sum_(k < i) p`_(i - k)
                                        * coef_inv_rec p m k
  end.

Definition coef_inv (p : {poly K}) i : K := coef_inv_rec p i i.

Lemma coef_inv_recE (p : {poly K}) m i : i <= m ->
  coef_inv_rec p m i = coef_inv p i.
Proof.
rewrite /coef_inv; elim: m {-2}m (leqnn m) i=> [k | m IHm].
  by rewrite leqn0 => /eqP -> i ; rewrite leqn0 => /eqP ->.
case=> [k i |k];  first by rewrite leqn0 => /eqP ->.
rewrite ltnS => le_km [ // | i ] ; rewrite ltnS => le_ik /=.
congr (_ * _) ; apply: eq_bigr => l _.
by rewrite !IHm 1?(leq_trans (leq_ord _)) // (leq_trans le_ik).
Qed.

Lemma coef_inv0 (p: {poly K}) : coef_inv p 0 = p`_0 ^-1.
Proof. by rewrite /coef_inv /= -lock. Qed.

Lemma coef_invS (p: {poly K}) j : coef_inv p j.+1 =
    -(p`_0 ^-1) * (\sum_(k < j.+1) p`_(j.+1 - k) * (coef_inv p k)).
Proof.
rewrite /coef_inv /= -lock; congr (_ * _) ; apply: eq_bigr => k _.
by rewrite coef_inv_recE // leq_ord.
Qed.

Definition unit_tfps : pred tfps := fun f => (f`_0 \in GRing.unit).

Definition inv_tfps f :=
    if f \in unit_tfps then [tfps s => coef_inv f s] else f.

Fact coef_inv_tfps_subproof f i : f \in unit_tfps ->
  (inv_tfps f)`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1 else
  - (f`_0 ^-1) * (\sum_(j < i) f`_(i - j) * (inv_tfps f)`_j).
Proof.
have [i_big|i_small] := ltnP; first by rewrite tfps_nth_default.
move=> f_unit; rewrite /inv_tfps f_unit !coef_tfps.
case: i => [|i] in i_small *; first by rewrite coef_inv0.
rewrite i_small coef_invS.
congr (_ * _); apply: eq_bigr => j _; rewrite coef_tfps ifT //.
by rewrite (leq_trans _ i_small) // leqW ?leq_ord.
Qed.

Fact nonunit_inv_tfps : {in [predC unit_tfps], inv_tfps =1 id}.
Proof. by move=> f; rewrite inE /inv_tfps /= => /negPf ->. Qed.

Fact unit_tfpsP f g : g * f = 1 -> unit_tfps f.
Proof.
move=> /val_eqP /eqP.
move/(congr1 (fun x => (val x)`_O)).
rewrite coef_modXn coef0M coefC eqxx /unit_tfps mulrC => h.
by apply/unitrPr; exists g`_0.
Qed.

Fact tfps_mulVr : {in unit_tfps, left_inverse 1 inv_tfps *%R}.
Proof.
move=> f f_unit; apply/val_inj; rewrite /inv_tfps f_unit /=.
apply/polyP => i; rewrite coef_modXn.
have [i_small | i_big] := ltnP; last first.
  by rewrite coefC gtn_eqF // (leq_trans _ i_big).
rewrite coefC; case: i => [|i] in i_small *.
  by rewrite coef0M coef_poly /= coef_inv0 mulVr.
rewrite coefM big_ord_recr coef_poly i_small subnn.
apply: canLR (addNKr _) _; rewrite addr0.
apply: canLR (mulrVK _) _; rewrite // mulrC mulrN -mulNr.
rewrite coef_invS; congr (_ * _); apply: eq_bigr => j _ /=.
by rewrite mulrC coef_poly (leq_trans _ i_small) 1?leqW.
Qed.

Definition tfps_comUnitRingMixin := ComUnitRingMixin
  tfps_mulVr unit_tfpsP nonunit_inv_tfps.

Canonical unit_tfpsRingType := UnitRingType tfps tfps_comUnitRingMixin.

Lemma coef_inv_tfps f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_(i - j) * f^-1`_j).
Proof. exact: coef_inv_tfps_subproof. Qed.

Fact val_mul_tfps f g : val (f * g) = (val f) * (val g) %% 'X^n.+1.
Proof. by []. Qed.

Fact val_exp_tfps f (m : nat) :
  val (f ^+ m) = (val f ^+ m) %% 'X^n.+1.
Proof.
elim: m => [|m ihm] //=; first by rewrite expr0 modCXn.
by rewrite exprS /= ihm Pdiv.IdomainUnit.modp_mul -?exprS.
Qed.

Lemma hmul_tfpsr1 f : f *h 1 = Tfpsp n (f`_0)%:P.
Proof.
apply/val_inj/polyP => s; rewrite coef_tfps coef_Tfpsp !coefC.
by case: s => [|s]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_tfps1r f : 1 *h f = Tfpsp n (f`_0)%:P.
Proof. by rewrite hmul_tfpsC hmul_tfpsr1. Qed.

Canonical tfps_comUnitRingType := [comUnitRingType of tfps].

Lemma unit_tfpsE f : (f \in GRing.unit) = (f`_0 \in GRing.unit).
Proof. by rewrite qualifE /= /unit_tfps. Qed.

Fact nth0_mul_tfps f g : (f * g)`_0 = f`_0 * g`_0.
Proof. by rewrite coef_Tfpsp coef0M. Qed.

Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
have [f_unit|] := boolP (f \is a GRing.unit); first by rewrite coef_inv_tfps.
move=> Hinv; rewrite (invr_out Hinv).
by move: Hinv; rewrite !unit_tfpsE => /invr_out ->.
Qed.

Definition scale_tfps (c : K) f := Tfpsp n (c *: (val f)).

Fact scale_tfpsA a b f : scale_tfps a (scale_tfps b f) = scale_tfps (a * b) f.
Proof.
apply/val_inj => /=.
rewrite Pdiv.IdomainUnit.modp_scalel // modp_modp ?monicXn //.
by rewrite -Pdiv.IdomainUnit.modp_scalel // scalerA.
Qed.

Fact scale_1tfps : left_id (1 : K) scale_tfps.
Proof.
move=> x; apply/val_inj => /=.
by rewrite scale1r modp_small // size_polyXn ltnS ?size_tfps.
Qed.

Fact scale_tfpsDl f: {morph scale_tfps^~ f : a b / a + b}.
Proof.
move=> a b ; apply/val_inj => /=.
by rewrite scalerDl Pdiv.IdomainUnit.modp_add.
Qed.

Fact scale_tfpsDr (a : K) : {morph scale_tfps a : f g / f + g}.
Proof.
by move=> f g; apply/val_inj => /=; rewrite scalerDr Pdiv.IdomainUnit.modp_add.
Qed.

Fact scale_tfpsAl (a : K) f g : scale_tfps a (f * g) = scale_tfps a f * g.
Proof.
apply/val_inj => /=.
rewrite Pdiv.IdomainUnit.modp_scalel // modp_small; last by rewrite ltn_modp expf_neq0 // polyX_eq0.
rewrite [in RHS]mulrC Pdiv.IdomainUnit.modp_mul // [in RHS]mulrC.
by rewrite -Pdiv.IdomainUnit.modp_scalel // -scalerAl.
Qed.

Definition tfps_lmodMixin := LmodMixin scale_tfpsA scale_1tfps
                                                       scale_tfpsDr scale_tfpsDl.

Canonical tfps_lmodType := Eval hnf in LmodType K tfps tfps_lmodMixin.
Canonical tfps_lalgType := Eval hnf in LalgType K tfps scale_tfpsAl.
Canonical tfps_algType := CommAlgType K tfps.
Canonical unit_tfpsAlgType := Eval hnf in [unitAlgType K of tfps].

Local Notation "c %:S" := (Tfpsp _ (c %:P)) (at level 2).

Fact onefE : 1 = 1 %:S.
Proof. by apply/val_inj => /=; rewrite modCXn. Qed.

End TruncatedPowerSeriesTheory.

Module Notations.

Local Open Scope tfps_scope.

Notation "{ 'tfps' K n }" := (tfps_of n (Phant K)) : tfps_scope.
Notation "[ 'tfps' s <= n => F ]" := (tfps_of_fun n (fun s => F)) : tfps_scope.
Notation "[ 'tfps' s => F ]" := [tfps s <= _ => F] : tfps_scope.
Notation "c %:S" := (Tfpsp _ (c %:P)) (at level 2) : tfps_scope.
Notation "f *h g" := (hmul_tfps f g) (at level 2) : tfps_scope.
Notation "f ^` () " := (deriv_tfps f) (at level 8) : tfps_scope.

End Notations.
Import Notations.

Local Open Scope tfps_scope.

Section MoreTruncatedPowerSeries.

Lemma Tfpsp_Tfpsp (K : idomainType) (m n : nat) (p : {poly K}) : m <= n ->
    Tfpsp m (Tfpsp n p) = Tfpsp m p.
Proof.
by move=> le_mn; apply/val_inj=> /=; rewrite modp_modp ?monicXn // dvdp_exp2l.
Qed.

End MoreTruncatedPowerSeries.

Section Truncated_Powerseries.

Variables (K : idomainType) (n : nat).

Lemma modp_opp (p q : {poly K}) :
  lead_coef q \is a GRing.unit -> (- p) %% q = - (p %% q).
Proof.
move=> lq_unit.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite !modp0.
exact: Pdiv.IdomainUnit.modp_opp.
Qed.

Fact Tfpsp_is_additive : additive (@Tfpsp K n).
Proof.
move => f g; apply/val_inj => /=.
by rewrite Pdiv.IdomainUnit.modp_add // modp_opp //.
Qed.

Canonical Tfpsp_additive := Additive Tfpsp_is_additive.

Lemma Tfpsp_is_multiplicative: multiplicative (@Tfpsp K n).
Proof.
split => [f g|]; last by apply/val_inj => /=; rewrite modCXn.
apply/val_inj => /=.
rewrite Pdiv.IdomainUnit.modp_mul // [in RHS]mulrC.
by rewrite Pdiv.IdomainUnit.modp_mul // mulrC.
Qed.

Canonical Tfpsp_rmorphism := AddRMorphism Tfpsp_is_multiplicative.

Fact TfpspZ (c : K) (p : {poly K}): (Tfpsp n (c *: p))=  c *:(Tfpsp n p).
Proof.
apply/val_inj => /=.
by rewrite -Pdiv.IdomainUnit.modp_scalel // modp_mod.
Qed.

Canonical Tfpsp_linear := AddLinear TfpspZ.

Canonical Tfpsp_lrmorphism := [lrmorphism of (Tfpsp n)].

(* tests *)
Fact tfps0 : Tfpsp n (0 : {poly K}) = 0.
Proof. by rewrite linear0. Qed.

Fact tfps1 : Tfpsp n (1 : {poly K}) = 1.
Proof. by rewrite rmorph1. Qed.


Lemma Tfpsp_is_unit (p : {poly K}) :
  ((Tfpsp n p) \is a GRing.unit) = (p`_0 \is a GRing.unit).
Proof. by rewrite unit_tfpsE nth0_Tfpsp. Qed.

Lemma TfpspE (p : {poly K}) : p %% 'X^ n.+1 = Tfpsp n p.
Proof. by apply/val_inj => /=. Qed.

Lemma tfps_is_cst (g : tfps K 0%N) : g = (g`_0) %:S.
Proof.
by apply/val_inj=> /=; rewrite modCXn //; apply: size1_polyC; rewrite size_tfps.
Qed.

Lemma tfpsC_mul : {morph (fun x => (x%:S : {tfps K n})) : a b / a * b >-> a * b}.
Proof.
move=> a b; apply/val_inj => /=; rewrite polyC_mul Pdiv.IdomainUnit.modp_mul //.
by rewrite [in RHS]mulrC Pdiv.IdomainUnit.modp_mul // mulrC.
Qed.

End Truncated_Powerseries.

Section MapTfps.

Variables (K L : fieldType) (n : nat) (f : {rmorphism K -> L}).

Implicit Type g h : {tfps K n}.

Definition map_tfps g := Tfpsp n (map_poly f (val g)).

Lemma map_tfpsM g h : map_tfps (g * h) = (map_tfps g) * (map_tfps h).
Proof.
apply/val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod rmorphM modp_mul.
by rewrite [in RHS]mulrC modp_mul mulrC.
Qed.

Fact map_tfps_is_additive : additive map_tfps.
Proof.
move => x y; apply/val_inj => /=.
by rewrite rmorphB /= modp_add modNp.
Qed.

Canonical map_tfps_additive := Additive map_tfps_is_additive.

Fact map_tfps_is_multiplicative : multiplicative map_tfps.
Proof.
split => [x y|]; first by rewrite map_tfpsM.
by apply/val_inj => /=; rewrite rmorph1 modCXn.
Qed.

Canonical map_tfps_rmorphism := AddRMorphism map_tfps_is_multiplicative.

Lemma map_tfpsZ (c : K) g : (map_tfps (c *: g)) =  (f c) *: (map_tfps g).
Proof.
apply/val_inj => /=.
by rewrite map_modp rmorphX /= map_polyX linearZ [in LHS]modp_scalel.
Qed.

Canonical map_tfps_linear := let R := ({tfps K n}) in
                       AddLinear (map_tfpsZ : scalable_for (f \; *:%R) map_tfps).

Canonical map_tfps_lrmorphism := [lrmorphism of map_tfps].

(* tests *)
Fact test_map_tfps0 : map_tfps 0 = 0.
Proof. by rewrite linear0. Qed.

Fact test_map_tfpsD g h : map_tfps (g + h) = (map_tfps g) + (map_tfps h).
Proof. by rewrite linearD. Qed.

Lemma Tfps_map_poly (p : {poly K}) :
                     @Tfpsp L n (p ^ f) = map_tfps (Tfpsp n p).
Proof. by apply/val_inj => /=; rewrite map_modp map_polyXn modp_mod. Qed.

Local Notation "g '^f'" := (map_tfps g) : tfps_scope.

Lemma map_hmul g h : (g *h h) ^f = (g ^f) *h (h ^f).
Proof.
apply/val_inj => /=; rewrite -polyP => i.
rewrite coef_modXn coef_map 2!coef_poly !coef_modXn.
by case: (i < n.+1) => //=; rewrite rmorphM !coef_map.
Qed.

Lemma map_tfps_injective : injective map_tfps.
Proof.
move => x y; move/val_eqP => /=.
rewrite ?(modp_small, (size_polyXn, size_map_poly, ltnS, size_tfps)) //.
by move/val_eqP => H; move: (map_poly_inj f H); apply/val_inj.
Qed.

End MapTfps.

Section IdFun.

Lemma map_poly_idfun (R : ringType) : map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma idfun_injective A : injective (@idfun A). Proof. done. Qed.
Canonical idfun_is_injmorphism (A : ringType) :=
    InjMorphism (@idfun_injective A).

End IdFun.

Lemma map_powerseries_idfun (K : fieldType) (m : nat) :
  map_tfps [rmorphism of (@idfun K)] =1 @idfun ({tfps K m}).
Proof.
move => p; apply: val_inj => /=.
by rewrite map_poly_idfun modp_small // size_polyXn ltnS size_tfps.
Qed.

Section Coefficient01.

Variables (K : idomainType) (n : nat).

Implicit Types (f g : {tfps K n}).

Definition coef0_is_0 : pred_class := fun f : {tfps K n} => f`_0 == 0.

Lemma coef0_is_0E f : (f \in coef0_is_0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Definition coef0_is_1 : pred_class := fun f : {tfps K n} => f`_0 == 1.

Lemma coef0_is_1E f : (f \in coef0_is_1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Definition exp f :=
  if f \notin coef0_is_0 then 0 else
  Tfpsp n (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (val f ^+i)).

Definition log f :=
  if f \notin coef0_is_1 then 0 else
  Tfpsp n (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - val f) ^+i)).

Fact c0_is_0_idealr : idealr_closed coef0_is_0.
Proof.
split => [|| a p q ]; rewrite ?coef0_is_0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefD q0_eq0 addr0 nth0_mul_tfps p0_eq0 mulr0.
Qed.

Fact c0_is_0_key : pred_key coef0_is_0. Proof. by []. Qed.

Canonical c0_is_0_keyed := KeyedPred c0_is_0_key.
Canonical c0_is_0_opprPred := OpprPred c0_is_0_idealr.
Canonical c0_is_0_addrPred := AddrPred c0_is_0_idealr.
Canonical c0_is_0_zmodPred := ZmodPred c0_is_0_idealr.

Definition c0_is_0_ntideal := idealr_closed_nontrivial c0_is_0_idealr.

Canonical c0_is_0_ideal := MkIdeal c0_is_0_zmodPred c0_is_0_ntideal.

Fact c0_is_0_prime : prime_idealr_closed coef0_is_0.
Proof.
by move => x y; rewrite -!topredE /= /coef0_is_0 nth0_mul_tfps mulf_eq0.
Qed.

Canonical coef0_is_0_pideal := MkPrimeIdeal c0_is_0_ideal c0_is_0_prime.

(* tests *)
Example zero_in_coef0_is_0 : 0 \in coef0_is_0.
Proof. by rewrite rpred0. Qed.

Example coef0_is_0D f g :
    f \in coef0_is_0 -> g \in coef0_is_0 -> f + g \in coef0_is_0.
Proof. by move=> hf hg; rewrite rpredD. Qed.

Example coef0_os_0N f : f \in coef0_is_0 -> (-f) \in coef0_is_0.
Proof. by move=> hf; rewrite rpredN. Qed.

Example coef0_is_0_prime_test f g :
    f * g \in coef0_is_0 -> (f \in coef0_is_0) || (g \in coef0_is_0).
Proof. by rewrite prime_idealrM. Qed.

Fact mulr_closed_c0_is_1 : mulr_closed coef0_is_1.
Proof.
split=> [|x y]; rewrite !coef0_is_1E ?coefC //.
by rewrite nth0_mul_tfps; move/eqP ->; move/eqP ->; rewrite mul1r.
Qed.

(*
Fact invr_closed_c0_is_1 : invr_closed coef0_is_1.
Proof.
move=> f; rewrite !coef0_is_1E nth0_inv; move/eqP ->.
by rewrite invr1.
Qed.
*)
Fact c0_is_1_key : pred_key coef0_is_1. Proof. by []. Qed.

Canonical c0_is_1_keyed := KeyedPred c0_is_1_key.

Canonical c0_is_1_MulrPred := MulrPred mulr_closed_c0_is_1.
(* Canonical c0_is_1_DivrPred := DivrPred invr_closed_c0_is_1. *)

(* tests *)
Example one_in_coef0_is_1 : 1 \in coef0_is_1.
Proof. by rewrite rpred1. Qed.

Example coef0_is_1M f g :
    f \in coef0_is_1 -> g \in coef0_is_1 -> f * g \in coef0_is_1.
Proof. by move=> hf hg; rewrite rpredM. Qed.

(*
Example coef0_is_1V f : f \in coef0_is_1 -> f^-1 \in coef0_is_1.
Proof. by move=> hf; rewrite rpredVr. Qed.

Example coef0_is_1_div f g :
    f \in coef0_is_1 -> g \in coef0_is_1 -> f / g \in coef0_is_1.
Proof. by move=> hf hg; rewrite rpred_div. Qed.
*)
End Coefficient01.

Section DivisionByX.

Variable (K : idomainType).

Definition divfX (m : nat) (f : {tfps K m}) := Tfpsp m.-1 (f %/ 'X).

Lemma divfXE (m : nat) (f : {tfps K m}) :
  f \in (@coef0_is_0 K m) -> divfX f = [tfps i => f`_i.+1].
Proof.
move/eqP/polyXP; rewrite Pdiv.IdomainUnit.dvdp_eq // /divfX; move/eqP => h.
rewrite [in RHS]h; apply/eq_tfps => i.
by rewrite coef_poly coef_modXn coefMX.
Qed.

End DivisionByX.

Lemma map_tfps_divfX (K L : fieldType) (f : {rmorphism K -> L})
  (m : nat) (g : tfps K m) :
  map_tfps f (divfX g) = divfX (map_tfps f g).
Proof.
apply/val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod map_divp map_polyX.
by rewrite [(_ ^ _ %% _)]modp_small // size_polyXn size_map_poly ltnS size_tfps.
Qed.

Section Derivative.

Variables (K : idomainType) (n : nat).

(* can be generalized with R ? *)
Lemma deriv_modp (p : {poly K}) :
    ((p %% 'X ^+ n.+1)^`() = (p ^`()) %% 'X ^+ n)%R.
Proof.
rewrite {2}[p](Pdiv.IdomainUnit.divp_eq (leadXn_unit _ n.+1)) derivD derivM.
rewrite !Pdiv.IdomainUnit.modp_add //.
rewrite -addrA [X in X + _]modp_eq0 ; last first.
rewrite dvdp_mull // dvdp_Pexp2l ?leqnSn // size_polyX //.
rewrite add0r [X in X + _]modp_eq0 ; last first.
  rewrite dvdp_mull // derivXn /= -scaler_nat.
  have [->|Sm_neq0] := eqVneq (n.+1)%:R (0 : K).
    by rewrite scale0r dvdp0.
  by rewrite dvdp_scaler.
rewrite add0r [RHS]modp_small // size_polyXn.
have [-> | p_modXSm_neq0] := eqVneq (p %% 'X^n.+1) 0.
+ by rewrite deriv0 size_poly0.
+ by rewrite (leq_trans _ (leq_modpXn n.+1 p)) // lt_size_deriv.
Qed.

Fact mod_deriv_tfps (m : nat) (f : {tfps K n}) : n <= m ->
  (val f)^`() %% 'X^m = ((val f)^`())%R.
Proof.
move => leq_nm; rewrite modp_small // size_polyXn ltnS.
rewrite (leq_trans _ leq_nm) // (leq_trans (leq_size_deriv _)) //.
have [->//|sfN0] := eqVneq (size (val f)) 0%N.
by rewrite -ltnS prednK ?size_tfps // lt0n.
Qed.

Lemma deriv_tfpsE (f : {tfps K n}) : deriv_tfps f = Tfpsp n.-1 (val f)^`().
Proof.
by apply/val_inj; apply/polyP => i; rewrite coef_poly coef_modXn coef_deriv.
Qed.

(* Local Notation "f ^` () " := (deriv_tfps f) (at level 8) : tfps_scope. *)

Fact deriv_tfps0 : (0 : {tfps K n}) ^`() = 0.
Proof.
apply/val_inj => /=; rewrite polyseq0; apply/polyP => i.
by rewrite coef_poly coefC mul0rn; case: (_ < _); case: i.
Qed.

(* can I simplify this proof ? *)
Lemma deriv_tfpsC (c : K) : c %:S ^`() = 0 :> {tfps _ n.-1}.
Proof.
apply/val_inj => /=; apply/polyP => i.
rewrite modp_small; last first.
  by rewrite size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
rewrite coef_poly coefC if_same polyseqC.
by case: (_ < _) => //; case: (_ == _); rewrite /= ?nth_nil mul0rn.
Qed.

Fact deriv_tfpsD (f g : {tfps K n}) : (f + g)^`() = f^`()%tfps + g^`()%tfps.
Proof.
apply/val_inj; apply/polyP => i; rewrite coefD !coef_poly coefD.
by case: (_ < _) => //=; rewrite ?addr0 // -mulrnDl.
Qed.

Fact deriv_tfpsZ (c : K) (f : {tfps K n}) : (c *: f) ^`() = c *: f ^`()%tfps.
Proof.
apply/val_inj; apply/polyP => i.
rewrite coef_poly coef_modXn !coefZ coef_modXn !coefZ coef_poly.
congr if_expr; rewrite [in RHS]fun_if mulr0 ltnS.
rewrite [LHS](@fun_if _ _ (fun x => x *+i.+1)) mul0rn.
move: f; case: n => [p|m p]; last by congr if_expr; rewrite mulrnAr.
by rewrite [p]tfps_is_cst coef_Tfpsp mul0rn mulr0 if_same.
Qed.

Fact deriv_tfps_is_linear : linear (@deriv_tfps K n).
Proof. by move => c f g; rewrite deriv_tfpsD deriv_tfpsZ. Qed.

Canonical deriv_tfps_additive := Additive deriv_tfps_is_linear.
Canonical deriv_tfps_linear := Linear deriv_tfps_is_linear.

(* tests *)
Example test_deriv_tfps0 : 0 ^`() = 0 :> {tfps K n.-1}.
Proof. by rewrite linear0. Qed.

Example test_deriv_tfpsD (f g : {tfps K n}) :
    (f + g)^`()%tfps = f^`()%tfps + g^`()%tfps.
Proof. by rewrite linearD. Qed.

End Derivative.

Section MoreDerivative.

Variable (K : idomainType) (m : nat).

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma pw_cst (f : {tfps K m}) : f ^` () = 0 -> {c : K | f = c %:S}.
Proof.
move: f; case: m => [f _| n f]; first by rewrite [f]tfps_is_cst; exists (f`_0).
rewrite deriv_tfpsE ; move/eqP ; rewrite -val_eqE /= => /eqP.
rewrite modp_small => [derivp_eq0|]; last first.
+ rewrite size_polyXn.
  have [->|fN0] := eqVneq f 0; first by rewrite linear0 size_poly0.
  by rewrite (leq_trans (lt_size_deriv _)) // size_tfps.
+ move: (p_cst char_K_is_zero derivp_eq0) => [c Hc].
  by exists c; apply/val_inj => /=; rewrite modCXn.
Qed.

Lemma pw_eq0 (f : {tfps K m}) :
    f ^` () = 0 -> {x : K | (val f).[x] = 0} -> f = 0.
Proof.
rewrite deriv_tfpsE /=; move/eqP ; rewrite -val_eqE /=.
have [-> _ _ // |fN0] := eqVneq f 0.
rewrite modp_small ?size_polyXn ?(leq_trans (lt_size_deriv _)) ?size_tfps //.
  move/eqP => derivp_eq0; move: (p_cst char_K_is_zero derivp_eq0) => [c Hc].
  rewrite Hc; move => [x hx]; rewrite hornerC in hx.
  by apply/val_inj => /=; rewrite Hc hx.
by rewrite (leq_trans (size_tfps _)) //; clear fN0 f; case: m => [|n].
Qed.

Lemma pw_eq (f g : {tfps K m}) :
               f ^` () = g ^` () -> {x : K | (val f).[x] = (val g).[x]} -> f = g.
Proof.
move => H [x Hx].
apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
apply: pw_eq0; first by rewrite linearB /= H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

Lemma deriv_Tfps0p (f : {tfps K 0}) : f ^` () = 0.
Proof.
by rewrite [f]tfps_is_cst deriv_tfpsE deriv_modp derivC mod0p rmorph0.
Qed.

Lemma deriv_tfpsM (f g : {tfps K m}) :
 (f * g) ^`() = f ^`()%tfps * (Tfpsp m.-1 g) + (Tfpsp m.-1 f) * g ^`()%tfps.
Proof.
move : f g; case: m => /= [f g | n f g].
  rewrite [f]tfps_is_cst [g]tfps_is_cst -tfpsC_mul !deriv_tfpsC mul0r mulr0.
  by rewrite addr0.
apply/val_inj; rewrite !deriv_tfpsE //=.
rewrite deriv_modp derivM Pdiv.IdomainUnit.modp_mul //.
rewrite [_ %% 'X^_ * _]mulrC !Pdiv.IdomainUnit.modp_mul //.
rewrite [_ %% 'X^_ * _]mulrC !Pdiv.IdomainUnit.modp_mul //.
rewrite modp_modp ?monicXn // -Pdiv.IdomainUnit.modp_add //.
by rewrite ![_^`() * _]mulrC.
Qed.

(*
Fact TfpsVf n p (f : {tfps K p}) :
  n <= p ->
  Tfpsp n (f^-1) = (Tfpsp n f) ^-1.
Proof.
move=> leq_mn.
have [/eqP p0_eq0|p0_neq0] := eqVneq f`_0 0.
  by rewrite ?(invr_out, unit_tfpsE, nth0_Tfpsp, negbK).
apply: (@mulrI _ (Tfpsp _ f)); rewrite ?divrr ?(unit_tfpsE, nth0_Tfpsp) //.
rewrite -rmorphM; apply/val_inj => /=.
rewrite -(@modp_modp K _ 'X^n.+1 'X^p.+1); last by rewrite dvdp_exp2l.
by rewrite -val_mul_tfps divrr ?unit_tfpsE // modCXn.
Qed.

Lemma deriv_tfpsV (f : {tfps K m}) :
  f \notin (@coef0_is_0 _ _) ->
  (f ^-1) ^`() = - f ^`()%tfps / Tfpsp m.-1 (f ^+ 2).
Proof.
move => p0_neq0.
move/eqP: (eq_refl (f / f)).
rewrite {2}divrr; last by rewrite unit_tfpsE.
move/(congr1 (@deriv_tfps K m)).
rewrite deriv_tfpsM onefE deriv_tfpsC.
move/eqP ; rewrite addrC addr_eq0 mulrC.
move/eqP/(congr1 (fun x => x / (Tfpsp m.-1 f))).
rewrite -mulrA divrr; last by rewrite unit_tfpsE nth0_Tfpsp.
rewrite mulr1 => ->.
rewrite !mulNr; congr (- _).
rewrite -mulrA; congr (_ * _).
rewrite TfpsVf // ?leq_pred // -invrM ?unit_tfpsE ?nth0_Tfpsp //; congr (_ ^-1).
rewrite -rmorphM /=; apply/val_inj => /=.
by rewrite modp_modp // dvdp_exp2l // (leq_ltn_trans (leq_pred _)).
Qed.

Lemma deriv_div_tfps (f g : {tfps K m}) :
  g`_0 != 0 ->
  (f / g) ^`() = (f^`()%tfps * Tfpsp m.-1 g - Tfpsp m.-1 f * g ^`()%tfps)
                                                    / (Tfpsp m.-1 (g ^+ 2)).
Proof.
move => g0_neq0.
rewrite deriv_tfpsM deriv_tfpsV // mulrBl mulrA mulrN mulNr.
congr (_ - _); rewrite -mulrA; congr (_ * _).
rewrite TfpsVf //; last exact: leq_pred.
rewrite expr2 ?leq_pred //.
have -> : Tfpsp m.-1 (g * g) = Tfpsp m.-1 ((val g) * g).
  apply/val_inj => /=.
  rewrite modp_modp ?dvdp_exp2l //.
  by clear g0_neq0 f g; case: m => //=.
rewrite rmorphM /= invrM ?Tfpsp_is_unit ?nth_Tfpsp //.
by rewrite mulrA divrr ?Tfpsp_is_unit ?nth_Tfpsp // mul1r.
Qed.
*)
End MoreDerivative.

Section Primitive.

Variables (K : idomainType) (n : nat).

Definition prim (p : {poly K}) :=
    \poly_(i < (size p).+1) (p`_i.-1 *+ (i != 0%N) / (i%:R)).

Definition prim_tfps (n : nat) : {tfps K n} -> {tfps K n.+1} :=
    fun f => [tfps s => f`_s.-1 *+ (s != 0%N) / s%:R].

Local Notation "\int p" := (prim p) (at level 2).

Lemma coef_prim (p : {poly K}) (i : nat) :
                        (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [| i]; first by rewrite eqxx coef_poly invr0 mulr0.
rewrite succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => //; rewrite mul0r.
Qed.

Lemma coef0_prim (p : {poly K}) : (\int p)`_0 = 0.
Proof. by rewrite coef_prim eqxx. Qed.

Lemma primC (c : K) : \int (c%:P) = c *: 'X.
Proof.
apply/polyP => i.
rewrite /prim /prim coef_poly size_polyC -[c *: 'X]coefK.
have [-> | c_neq0 ] := eqVneq c 0.
  rewrite eqxx /= scale0r size_poly0 coef_poly ltn0; case: i => [|i].
    by rewrite invr0 mulr0.
    by rewrite coefC.
rewrite c_neq0 /= coef_poly size_scale // size_polyX coefZ coefX.
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

Lemma prim_tfpsXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
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

Hypothesis char_K_is_zero : [char K] =i pred0.

Fact natmul_inj (m : nat) : (m%:R == 0 :> K) = (m == 0%N).
Proof. by move/(charf0P K)/(_ m) : char_K_is_zero. Qed.

Lemma pred_size_prim (p : {poly K}) : (size (prim p)).-1 = size p.
Proof.
have [->|/negbTE p_neq0] := eqVneq p 0; first by rewrite prim0 size_poly0.
rewrite size_poly_eq // size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

(*
Lemma primK : cancel prim (@deriv K).
Proof.
move => p.
rewrite /prim -{3}[p]coefK ; apply/polyP => i.
rewrite coef_deriv !coef_poly ltnS.
case: (_ < _); last by rewrite mul0rn.
by rewrite eqn0Ngt ltn0Sn -mulr_natr mulrAC -mulrA divff ?natmul_inj // mulr1.
Qed.
*)

Fact prim_tfps_is_linear : linear (@prim_tfps n).
Proof.
move => k p q; apply/val_inj => /=.
apply/polyP => i.
rewrite coefD coef_modXn coefZ !coef_poly.
case: (i < _) => /=; last by rewrite addr0.
rewrite coefD mulrnDl mulrDl; congr (_ + _); rewrite coef_modXn coefZ.
case: i => [|i /=]; first by rewrite eqxx mulr0n invr0 !mulr0.
have [_|/leq_sizeP big_i] := ltnP; first by rewrite mulrA.
rewrite mul0rn mul0r big_i; first by rewrite mul0rn mul0r mulr0.
by rewrite size_tfps.
Qed.

Canonical prim_tfps_linear := Linear prim_tfps_is_linear.

(* tests *)
Fact prim_tfps0 : @prim_tfps n 0 = 0.
Proof. exact: linear0. Qed.

Fact prim_tfpsD : {morph (@prim_tfps n) : p q / p + q}.
Proof. exact: linearD. Qed.

(*
Lemma prim_tfpsK : cancel (@prim_tfps n) (@deriv_tfps K n.+1).
Proof.
move=> p; apply/val_inj; apply/polyP => i; rewrite coef_poly.
have [small_i|/leq_sizeP big_i] := ltnP; last by rewrite big_i // size_tfps.
rewrite coef_poly /= ltnS small_i mulr1n -mulr_natr -mulrA [X in _ * X]mulrC.
by rewrite divff ?natmul_inj // mulr1.
Qed.
*)
Lemma coef0_prim_tfps (p : tfps K n) : (prim_tfps p)`_0 = 0.
Proof. by rewrite coef_poly eqxx mulr0n invr0 mulr0. Qed.
(*
Lemma deriv_tfpsK :
    {in @coef0_is_0 K n.+1, cancel (@deriv_tfps _ _) (@prim_tfps _)}.
Proof.
move=> f; rewrite coef0_is_0E => /eqP f0_eq0.
apply/val_inj; apply/polyP => i; rewrite coef_poly.
have [|/leq_sizeP big_i] := ltnP; last by rewrite big_i // size_tfps.
case: i => [_|i]; first by rewrite eqxx mulr0n mul0r f0_eq0.
rewrite ltnS => small_i; rewrite coef_poly small_i -lt0n ltn0Sn -mulr_natr mulr1.
by rewrite -mulr_natr -mulrA divff ?natmul_inj // mulr1.
Qed.
*)
End Primitive.

Section Composition.

Variables (K : idomainType) (n : nat).

Definition comp_tfps m (g p : {tfps K m}) :=
  if g \in (@coef0_is_0 K m) then Tfpsp m (comp_poly g p) else 0.

Local Notation "f \So g" := (comp_tfps g f) (at level 2) : tfps_scope.

Lemma comp_tfps_coef0_neq0 (f g : {tfps K n}) :
                                       g \notin (@coef0_is_0 K n) -> f \So g = 0.
Proof. by move/negbTE => p0_neq0; rewrite /comp_tfps p0_neq0. Qed.

Lemma comp_tfps_coef0_eq0 (f g : {tfps K n}) :
                g \in (@coef0_is_0 K n) -> f \So g = Tfpsp n (comp_poly g f).
Proof. by move => f0_eq0 ; rewrite /comp_tfps f0_eq0. Qed.

Section Variable_f.

Variable (f : {tfps K n}).

Lemma comp_tfps0r : f \So 0 = (f`_0) %:S.
Proof. by rewrite comp_tfps_coef0_eq0 ?rpred0 // comp_poly0r. Qed.

Lemma comp_tfpsr0 : 0 \So f = 0.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in (@coef0_is_0 K n)).
+ by rewrite comp_tfps_coef0_eq0 // comp_poly0 rmorph0.
+ by rewrite comp_tfps_coef0_neq0.
Qed.

(* is there a better statement ? *)
Lemma comp_tfpsC (c : K) : c%:S \So f = (c * (f \in (@coef0_is_0 K n))%:R) %:S.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in (@coef0_is_0 K n)).
+ by rewrite comp_tfps_coef0_eq0 //= modCXn // comp_polyC mulr1.
+ by rewrite mulr0 Tfpsp0 comp_tfps_coef0_neq0.
Qed.

Lemma comp_tfpsCf (c : K) : f \So (c%:S) = (f`_0 * (c == 0)%:R) %:S.
Proof.
have [->| /negbTE c_neq0] := eqVneq c 0.
  by rewrite eqxx mulr1 rmorph0 comp_tfps0r.
rewrite comp_tfps_coef0_neq0; last first.
  by rewrite coef0_is_0E nth0_Tfpsp coefC eqxx negbT.
by rewrite c_neq0 mulr0 rmorph0.
Qed.

Hypothesis (f0_is_0 : f \in (@coef0_is_0 K n)).

Fact comp_tfps_is_additive : additive (comp_tfps f).
Proof.
move => u v; rewrite !comp_tfps_coef0_eq0 //.
by apply/val_inj; rewrite rmorphB /= Pdiv.IdomainUnit.modp_add // modp_opp.
Qed.

Fact comp_tfps_is_linear : linear (comp_tfps f).
Proof.
move => a q r.
rewrite !comp_tfps_coef0_eq0 // !rmorphD /=.
by rewrite Pdiv.IdomainUnit.modp_scalel // mod_tfps // !linearZ.
Qed.

End Variable_f.
End Composition.

Section MoreComposition.

Local Notation "f \So g" := (comp_tfps g f) (at level 2) : tfps_scope.

Local Notation "f ^` () " := (deriv_tfps f) (at level 8) : tfps_scope.

Lemma deriv_tfps_comp (K : idomainType) (m : nat) (f g : {tfps K m}):
  f \in (@coef0_is_0 K m) ->
  deriv_tfps (g \So f) = (g ^`() \So (Tfpsp m.-1 f)) * f^`()%tfps.
Proof.
rewrite !deriv_tfpsE //.
move: f g; case: m => [f g g0_eq0| m f g g0_eq0].
+ apply/val_inj => /=.
  rewrite [f]tfps_is_cst [g]tfps_is_cst Tfpsp_Tfpsp // comp_tfpsC !deriv_modp.
  by rewrite !derivC !mod0p mulr0 mod0p.
+ rewrite /= comp_tfps_coef0_eq0 // comp_tfps_coef0_eq0 ?p0_is_0; last first.
    by rewrite coef0_is_0E nth0_Tfpsp -coef0_is_0E.
  apply/val_inj => /=.
  rewrite deriv_modp deriv_comp modp_mod Pdiv.IdomainUnit.modp_mul //.
  rewrite mulrC -[LHS]Pdiv.IdomainUnit.modp_mul // mulrC.
  congr (modp _) ; congr (_ * _).
  rewrite [deriv g %% 'X^m.+1]modp_small ; last first.
  rewrite size_polyXn (leq_ltn_trans (leq_size_deriv _)) //.
  have [-> //|] := eqVneq (size g) 0%N.
  by rewrite -lt0n => sp_gt0; rewrite prednK // size_tfps.
  rewrite (Pdiv.IdomainUnit.divp_eq (leadXn_unit _ m.+1) (val f)).
  rewrite Pdiv.IdomainUnit.modp_add // modp_mull add0r modp_mod.
  rewrite !comp_polyE !modp_sumn /=; apply: eq_bigr => i _.
  rewrite !modp_scalel; congr (_ *: _).
  rewrite exprDn big_ord_recr /= subnn expr0 mul1r binn mulr1n modp_add.
  rewrite modp_sumn /= (eq_bigr (fun j => 0)) => [|j _].
    by rewrite big1_eq add0r.
  rewrite -scaler_nat modp_scalel; apply/eqP.
  rewrite scaler_eq0 ; apply/orP; right.
  apply/eqP; apply: modp_eq0.
  by rewrite dvdp_mulr // exprMn dvdp_mull // dvdp_exp // subn_gt0.
Qed.

End MoreComposition.

Section Exponential.

Variables (K : fieldType) (m : nat).

Lemma expr_coef0_is_0 (n : nat) : m < n ->
    {in @coef0_is_0 K m, forall f, f^+n = 0}.
Proof.
move => lt_mn f; rewrite coef0_is_0E; move/eqP.
rewrite -horner_coef0 => /polyXsubCP p0_eq0.
rewrite polyC0 subr0 in p0_eq0; apply/val_inj => /=.
rewrite val_exp_tfps; apply/modp_eq0P.
by rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) lt_mn)) // dvdp_exp2r.
Qed.

(* to generalize *)
Lemma coef0_1subf_is_0 f :
  f \in (@coef0_is_1 K m) -> (1 - f) \in (@coef0_is_0 K m).
Proof.
rewrite ?coef0_is_0E ?coef0_is_1E.
rewrite -!horner_coef0 -!horner_evalE rmorphB /= !horner_evalE hornerC.
by move=> /eqP -> ; rewrite subrr.
Qed.

Lemma exp_coef0_is_0 f : f \in @coef0_is_0 K m ->
  exp f = Tfpsp m (\sum_(i < m.+1) ((i`! %:R) ^-1) *: ((val f) ^+i)).
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_isnt_0 f : f \notin @coef0_is_0 K m -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0: exp (0 : {tfps K m}) = 1.
Proof.
apply/val_inj/polyP=> j.
rewrite exp_coef0_is_0 ?rpred0 //=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == O)%:R))=> [|i]; last first.
  by case: (_ i) => [|k]; rewrite expr0n ?eqxx ?fact0 ?invr1 ?scale1r ? scaler0.
rewrite -(big_mkord predT (fun i => (i == _)%:R)) /=.
rewrite big_ltn // eqxx big_nat /= big1 => [|i /andP [hi _]]; last first.
  by rewrite eqn0Ngt hi.
by rewrite addr0 modCXn.
Qed.

Lemma expC (c : K) : exp (c %:S) = (c == 0)%:R %:S :> {tfps K m}.
Proof.
have [p0eq0 | p0N0] := boolP (c %:S \in @coef0_is_0 K m).
+ rewrite coef0_is_0E nth0_Tfpsp coefC /= in p0eq0.
  move: p0eq0 => /eqP p0eq0.
  rewrite p0eq0 eqxx exp_coef0_is_0 //=; last by rewrite rmorph0 rpred0.
  rewrite mod0p -(big_mkord predT (fun i => i`!%:R^-1 *: 0%:P ^+ i)) /=.
  rewrite big_ltn // fact0 expr0 invr1 big_nat_cond.
  rewrite (eq_bigr (fun i => 0))=> [ | i /andP [/andP [Hi _] _] ] ; last first.
    by rewrite expr0n eqn0Ngt Hi /= scaler0.
  by rewrite scale1r big1_eq addr0.
+ rewrite exp_coef0_isnt_0 //.
  rewrite coef0_is_0E nth0_Tfpsp coefC /= in p0N0.
  by move/negbTE: p0N0 => ->; rewrite rmorph0.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma exp_is_morphism :
            {in (@coef0_is_0 K m) &, {morph (@exp _ _) : f g / f + g >-> f * g}}.
Proof.
move => f g f0_eq0 g0_eq0 /=.
rewrite ?(exp_coef0_is_0, rpredD) //.
apply/val_inj => /=; apply/val_inj => /=.
rewrite modp_mul mulrC modp_mul -mulrC.
rewrite coef0_is_0E -!horner_coef0 in f0_eq0 g0_eq0.
move/eqP: g0_eq0 ; move/eqP : f0_eq0.
move: f g => [f fr] [g gr] /=.
rewrite !horner_coef0 => f0_eq0 g0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *:
         (\sum_(j < i'.+1) f ^+ (i' - j) * g ^+ j *+ 'C(i', j)))); last first.
  by move => i _ ; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i' .+1)
        ((j`! * (i' -j)`!)%:R) ^-1 *: (f ^+ (i' - j) * g ^+ j)))); last first.
  move => [i i_lt_Sn] _ /=.
  rewrite scaler_sumr; apply: eq_bigr => [ /= [j j_lt_Si]] _ /=.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl; congr(_ *: _).
  have factr_neq0 k : k`!%:R != 0 :> K.
    by rewrite (proj1 (charf0P _)) // -lt0n fact_gt0.
  apply: (mulfI (factr_neq0 i)); rewrite mulVKf //.
  have den_neq0 :  (j`! * (i - j)`!)%:R != 0 :> K by rewrite natrM mulf_neq0.
  by apply: (mulIf den_neq0) ; rewrite mulfVK // -natrM bin_fact.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < m.+1)
                    ((i'`! * j`!)%:R^-1) *: (f ^+ i' * g ^+ j)))); last first.
  move => i _.
  rewrite (big_distrr _ _ _) /=.
  apply: eq_bigr => j _ /=.
  rewrite -scalerAl -scalerCA -scalerAl scalerA -invrM ?unitfE; last 2 first.
  + move/(charf0P K)/(_ (j`!)%N) : char_K_is_zero ->.
    by rewrite -lt0n fact_gt0.
  + move/(charf0P K)/(_ (i`!)%N) : char_K_is_zero ->.
    by rewrite -lt0n fact_gt0.
  by rewrite -natrM mulnC.
have -> : (\sum_(i < m.+1) \sum_(j < m.+1)
  (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^m.+1 =
  (\sum_(i < m.+1) \sum_(j < m.+1 | i+j <= m)
  (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^m.+1.
  rewrite !modp_sumn ; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !modp_sumn.
  rewrite (bigID (fun j => i + (nat_of_ord j) <= m)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= m))
                      (fun j => ((i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^m.+1)).
  apply: big1_seq => /= n.
  rewrite -ltnNge ; move/andP => [ n_lt_addim _].
  apply/modp_eq0P.
  rewrite dvdp_scaler ; last first.
  rewrite invr_eq0.
    move/(charf0P K)/(_ (i`! * n`!)%N) : char_K_is_zero ->.
    by rewrite muln_eq0 negb_or -!lt0n !fact_gt0.
    rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_addim)) // exprD.
    by rewrite dvdp_mul // dvdp_exp2r // ; apply/polyXP.
apply: (congr1 (fun x => polyseq x)).
apply: (congr1 (fun x => modp x (GRing.exp (polyX K) (S m)))).
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < m.+1 |
        i' + j < m.+1) (i'`! * j`!)%:R^-1 *: (f ^+ i' * g ^+ j))); last first.
  move => i _.
  by apply: eq_bigr.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < i'.+1)
           (j`! * (i' - j)`!)%:R^-1 *: (f ^+ j * g ^+ (i' - j)))); last first.
  move => i _.
  rewrite /=.
  rewrite -(big_mkord predT (fun j => (j`! * (i - j)`!)%:R^-1 *:
                                                       (f ^+ (i - j) * g ^+ j))).
  rewrite big_nat_rev big_mkord add0n.
  apply: eq_bigr => j _.
  by rewrite !subSS subnBA -1?ltnS // !addKn mulnC.
by rewrite (triangular_index_bigop _
                      (fun i j => (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j))) /=;
  last exact: ltnSn.
Qed.

Lemma log_coef0_is_1 f : f \in @coef0_is_1 K m ->
  log f = Tfpsp m (- \sum_(1 <= i < m.+1) ((i %:R) ^-1) *: ((1 - (val f)) ^+i)).
Proof. by rewrite /log => ->. Qed.

Lemma log_coef0_isnt_1 f : f \notin @coef0_is_1 K m -> log f = 0.
Proof. by rewrite /log => /negPf ->. Qed.

Lemma log1 : log (1 : {tfps K m}) = 0.
Proof.
apply/val_inj/polyP=> j; rewrite log_coef0_is_1 ?rpred1 // coef0 coef_Tfpsp.
case: ifP => // j_small; rewrite coefN big1 ?coef0 ?oppr0 //.
by move=> [|i]; rewrite subrr expr0n ?eqxx ?invr0 ?scale0r ?scaler0.
Qed.

(* is there a better statement ? something like: *)
(* Lemma coef0_exp f : (exp f)`_0 = (f \notin coef0_is_0)%:R. *)
Lemma coef0_exp f : f \in @coef0_is_0 K m -> (exp f)`_0 = 1.
Proof.
move => f0_eq0.
rewrite exp_coef0_is_0 // coef_modXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorph_sum /=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == 0%N)%:R)) => [ | [i _] _ ] /=.
+ rewrite -(big_mkord predT (fun i => ((i == _)%:R))) big_ltn ?ltnS //.
  rewrite eqxx /= -natr_sum big_nat_cond.
  rewrite (eq_big (fun i => (0 < i < m.+1)) (fun i => 0%N)) => [ | i | i ].
- by rewrite big1_eq addr0.
- by rewrite andbT.
  by rewrite andbT => /andP [/lt0n_neq0/negbTE -> _].
+ rewrite linearZ /= rmorphX /= horner_evalE horner_coef0.
  move: f0_eq0 ; rewrite coef0_is_0E => /eqP ->.
  rewrite expr0n ; case: i => [ | i'].
- by rewrite fact0 invr1 mul1r.
- by rewrite eqn0Ngt -leqNgt ltn0 mulr0.
Qed.

Lemma coef0_log (f : {tfps K m}) : (log f)`_0 = 0.
Proof.
have [f0_eq1|f0_neq1] := boolP (f \in @coef0_is_1 K m); last first.
  by rewrite log_coef0_isnt_1 // coefC.
rewrite log_coef0_is_1 // coef_modXn ltn0Sn -horner_coef0.
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

End Exponential.

Section MoreExponential.

Variable (K : fieldType).

Local Notation "f ^` ()" := (deriv_tfps f) (at level 8) : ring_scope.

Lemma deriv_tfps_exp (m : nat) (f : {tfps K m}) (n : nat) :
    (f ^+ n)^` () = f^` () * (Tfpsp m.-1 f) ^+ n.-1 *+ n.
Proof.
elim: n => /= [|n IHn]; first by rewrite expr0 mulr0n onefE deriv_tfpsC.
rewrite exprS deriv_tfpsM {}IHn (mulrC (_ f)) val_exp_tfps /=.
rewrite mulrC -mulrnAr mulrCA -mulrDr -mulrnAr; congr (_ * _).
rewrite Tfpsp_modp; last by clear f; case: m.
rewrite rmorphX /= mulrnAr -exprS; case: n => /= [|n]; rewrite -?mulrS //.
by rewrite !expr0 mulr0n addr0.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.
Hint Resolve char_K_is_zero.

Lemma deriv_exp (m : nat) (p : {tfps K m}) :
  (exp p)^` () = (p^` ()) * (Tfpsp m.-1 (exp p)).
Proof.
move: p ; case: m => /= [p | n p].
  by rewrite [p]tfps_is_cst deriv_tfpsC mul0r expC deriv_tfpsC.
have [p0_eq0 | p0_neq0] := boolP (p \in (@coef0_is_0 K n.+1)) ; last first.
  by rewrite exp_coef0_isnt_0 // deriv_tfps0 rmorph0 mulr0.
rewrite !exp_coef0_is_0 //= !deriv_tfpsE //=; apply/val_inj => /=.
rewrite deriv_modp modp_modp ?dvdp_exp2l ?monicXn //.
rewrite modp_modp ?dvdp_exp2l ?monicXn //.
rewrite deriv_sum -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= modp_add modp_scalel.
rewrite modX_eq0 //; last by apply/eqP; rewrite -coef0_is_0E.
rewrite scaler0 addr0 modp_mul modp_mul2 mulr_sumr.
rewrite -(big_mkord predT (fun i => deriv (i`!%:R^-1 *: (val p) ^+ i))) /=.
rewrite big_nat_recl // expr0 linearZ /= derivC scaler0 add0r.
congr (_ %% _); apply: eq_bigr => i _.
rewrite linearZ /= deriv_exp /= -scalerCA -scaler_nat.
rewrite scalerA -scalerAl; congr (_ *: _).
rewrite factS natrM /= invrM ?unitfE ?natmul_inj // -?lt0n ?fact_gt0 //.
rewrite -mulrA [X in _ * X]mulrC.
by rewrite divff ?natmul_inj // -?lt0n ?fact_gt0 // mulr1.
Qed.

Lemma deriv_log (m : nat) (f : {tfps K m}) :
       f \in (@coef0_is_1 K m) -> (log f) ^` () = (f )^` () / (Tfpsp m.-1 f).
Proof.
move: f; case: m => [|m]; move => f.
rewrite [f]tfps_is_cst coef0_is_1E nth0_Tfpsp coefC eqxx => /eqP ->.
by rewrite !deriv_Tfps0p mul0r.
move => f0_is_1.
rewrite log_coef0_is_1 // rmorphN rmorph_sum linearN raddf_sum -sumrN.
rewrite big_nat.
rewrite (eq_bigr (fun i => (f )^` () * ((1 - (Tfpsp m f)) ^+ i.-1))) =>
                                                  [|i /andP [hi _]]; last first.
+ rewrite linearZ rmorphX /= deriv_tfpsZ rmorphB rmorph1 deriv_tfps_exp.
  rewrite linearB rmorphB rmorph1 onefE /= deriv_tfpsC sub0r /= Tfpsp_modp //.
  rewrite -scaler_nat scalerA mulrC divff ?natmul_inj //-?lt0n // scale1r mulNr.
  rewrite  opprK; congr (_ * _); apply/val_inj => /=.
  by rewrite modp_small // size_polyXn ltnS size_tfps.
+ rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : Tfpsp m f \is a GRing.unit.
    rewrite Tfpsp_is_unit.
    move: f0_is_1 ; rewrite coef0_is_1E => /eqP ->.
    exact: unitr1.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  apply/val_inj => /=.
  rewrite val_exp_tfps modX_eq0 ?subr0 // coefB coef1 eqxx.
  rewrite coef0_is_1E in f0_is_1.
  rewrite nth0_Tfpsp; move/eqP : f0_is_1 ->.
  by rewrite subrr.
Qed.

Lemma cancel_log_exp (m : nat) :
    {in @coef0_is_0 K m, cancel (@exp K m) (@log K m)}.
Proof.
move => f f0_eq0 /=.
  apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
  apply: (pw_eq0 char_K_is_zero).
- rewrite linearB /= deriv_log ?coef0_is_1E ?coef0_exp //.
  rewrite deriv_exp -mulrA divrr ?mulr1 ?subrr // Tfpsp_is_unit.
  by rewrite coef0_exp // unitr1.
- exists 0; rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0.
  by rewrite coef0_log sub0r; apply/eqP; rewrite oppr_eq0 -coef0_is_0E.
Qed.

Lemma exp_inj (m : nat) : {in @coef0_is_0 K m &, injective (@exp K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= H.
have : p^`()%tfps * (Tfpsp m.-1 (exp p)) = q^`()%tfps * (Tfpsp m.-1 (exp p)).
  by rewrite {2}H -!deriv_exp H.
move/mulIr => H_deriv; apply: pw_eq => //.
+ apply: H_deriv.
  by rewrite Tfpsp_is_unit coef0_exp // unitr1.
+ exists 0 ; rewrite !horner_coef0.
  by move: p0_eq0 q0_eq0 ; rewrite !coef0_is_0E => /eqP -> /eqP ->.
Qed.

(*
Lemma log_inj (m : nat) : {in @coef0_is_1 K m &, injective (@log K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= Hlog.
have H: (p/q) ^` () = 0.
  rewrite deriv_div_tfps; last first.
    by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
  have -> : p^`()%tfps * Tfpsp m.-1 q - Tfpsp m.-1 p * q^`()%tfps = 0 ;
    last by rewrite mul0r.
  apply/eqP; rewrite subr_eq0 [Tfpsp m.-1 p * q^`()%tfps]mulrC.
  rewrite -eq_divr ?Tfpsp_is_unit ; last 2 first.
      by move: p0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
      by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
  by move/(congr1 (@deriv_tfps K m)) : Hlog; rewrite !deriv_log // => ->.
move: (pw_cst char_K_is_zero H) => [c Hpq].
have Hc : c = 1.
  move/(congr1 (fun x => x * q)): Hpq.
  rewrite mulrAC -mulrA divrr ; last first.
    rewrite unit_tfpsE.
    rewrite coef0_is_1E in q0_eq0.
    by move/eqP: q0_eq0 ->; apply: oner_neq0.
  rewrite mulr1; move/val_eqP => /=.
  rewrite modCXn // modp_small; last first.
    rewrite mul_polyC (leq_ltn_trans (size_scale_leq _ _)) //.
    by rewrite size_polyXn; apply: size_tfps.
  move/eqP; move/(congr1 (fun x => x.[0])).
  rewrite !horner_coef0 coef0M.
  move: p0_eq0; rewrite coef0_is_1E => /eqP ->.
  move: q0_eq0; rewrite coef0_is_1E => /eqP ->.
  by rewrite coefC eqxx mulr1.
move: Hpq; rewrite Hc; move/(congr1 (fun x => x * q)).
rewrite mulrAC -mulrA divrr ; last first.
  rewrite unit_tfpsE.
  rewrite coef0_is_1E in q0_eq0.
  by move/eqP: q0_eq0 ->; apply: oner_neq0.
rewrite mulr1; move/val_eqP => /=.
rewrite modp_mul2 mul1r modp_small //; last first.
  by rewrite size_polyXn; apply: size_tfps.
by move/eqP => H2; apply/val_inj.
Qed.

Lemma cancel_exp_log (m : nat) : {in @coef0_is_1 K m, cancel (@log K m) (@exp K m)}.
Proof.
move => p p0_eq1 /=.
apply: log_inj => //.
  rewrite coef0_is_1E.
  apply/eqP; rewrite coef0_exp //.
  by rewrite coef0_is_0E; apply/eqP; rewrite coef0_log.
by rewrite cancel_log_exp // coef0_is_0E coef0_log.
Qed.
 *)

End MoreExponential.
