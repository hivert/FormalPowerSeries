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
From mathcomp Require Import rat ssrnum.

Require Import auxresults truncpoly.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Catalan.

Variable (C : nat -> nat).

Hypothesis C0 : C 0 = 1%N.
Hypothesis CS : forall n : nat, C n.+1 = \sum_(i < n.+1) C i * C (n - i).

Example C1 : C 1 = 1.
Proof. by rewrite !(CS, big_ord_recl, big_ord0, C0); compute. Qed.
Example C2 : C 2 = 2.
Proof. by rewrite !(CS, big_ord_recl, big_ord0, C0); compute. Qed.
Example C3 : C 3 = 5.
Proof. by rewrite !(CS, big_ord_recl, big_ord0, C0); compute. Qed.
Example C4 : C 4 = 14.
Proof. by rewrite !(CS, big_ord_recl, big_ord0, C0); compute. Qed.
Example C5 : C 5 = 42.
Proof. by rewrite !(CS, big_ord_recl, big_ord0, C0); compute. Qed.


Import GRing.Theory.

Local Definition Rat := [fieldType of rat].
Local Definition charRat := Num.Theory.char_num [numDomainType of Rat].
Local Definition nat_unit := nat_unit_field charRat.
Local Definition fact_unit := TruncPolyUnitRing.fact_unit nat_unit.
Hint Resolve nat_unit.
Hint Resolve fact_unit.

Section GenSeries.

Local Open Scope ring_scope.
Local Open Scope trpoly_scope.

Variable n : nat.
Definition FC : {trpoly Rat n} := [trpoly i => (C i)%:R ].

Lemma FC_in_coef0_is_1 : FC \in coef0_is_1.
Proof. by rewrite coef0_is_1E coef_trpoly_of_fun /= C0. Qed.

Proposition FC_eq : FC = 1 + \X * FC ^+ 2.
Proof.
rewrite /FC; apply/trpolyP => i le_in.
rewrite coef_trpoly_of_fun coefD coef1 coef_trpolyMX le_in.
case: i le_in => [|i] lt_in; first by rewrite C0 addr0.
rewrite add0r CS [i.+1.-1]/= expr2 /= trXnE coef_trXn (ltnW lt_in).
rewrite coefM natr_sum; apply eq_bigr => [[j]]; rewrite /= ltnS => le_ji _.
rewrite natrM !coef_poly.
rewrite (leq_trans (leq_ltn_trans le_ji lt_in) _) //.
by rewrite ltnS (leq_trans (leq_subr _ _) (ltnW lt_in)).
Qed.

Import TruncPolyUnitRing.

Lemma mulr_nat i (f : {trpoly Rat n}) : i%:R *: f = i%:R * f.
Proof. by rewrite scaler_nat -[f *+ i]mulr_natr mulrC. Qed.

Theorem FCE : \X * FC = 2%:R^-1 *: (1 - \sqrt (1 - 4%:R *: \X)).
Proof.
have : (2%:R *: \X * FC - 1) ^+ 2 = 1 - 4%:R *: \X.
  apply/eqP; rewrite !mulr_nat sqrrB1 !exprMn 2!expr2 -natrM.
  rewrite mulrA -subr_eq0 opprB [_ - 1]addrC addrA addrK addrC addrA.
  rewrite -{1}(mulr1 (4%:R * _)) -[X in _ + X + _]mulrA -mulrDr -FC_eq.
  by rewrite -[_ *+ 2]mulr_natl !mulrA -natrM subrr.
have co1 : 1 - 4%:R *: \X \in @coef0_is_1 Rat n.
  by rewrite mulr_nat coef0_is_1E coefD mulrC coefN coef_trpolyMX coef1 /= subr0.
move/(sqrtE nat_unit) => /(_ co1) [|Heq].
  move/(congr1 (fun x : {trpoly _ _ } => x`_0)).
  rewrite mulr_nat coefB -mulrA mulrC -mulrA coef_trpolyMX coef1.
  rewrite (eqP (coef0_is_1_expr _ _)) /= => /eqP.
  rewrite -subr_eq0 add0r -oppr_eq0 opprD opprK -mulr2n => /eqP Habs.
  by have:= charRat 2; rewrite !inE Habs /= eq_refl.
have neq20 : 2%:R != 0 :> Rat by rewrite Num.Theory.pnatr_eq0.
apply (scalerI neq20); rewrite scalerA divff // scale1r -Heq.
by rewrite addrC subrK scalerAl.
Qed.

Lemma expr_prod i (x : Rat) : x ^+ i = \prod_(j < i) x.
Proof.
elim: i => [|i IHi]; first by rewrite expr0 big_ord0.
by rewrite big_ord_recl -IHi exprS.
Qed.

Theorem coefFC i : (i < n)%N -> FC`_i = i.*2`!%:R / i`!%:R /i.+1`!%:R.
Proof.
move=> Hi.
have:= congr1 (fun x : {trpoly _ _ } => x`_i.+1) FCE.
rewrite coef_trpolyMX Hi ![X in (X = _)]/= => ->.
rewrite coefZ coefB coef1 sub0r -scaleNr coef_expr1cX ?{}Hi //.
rewrite mulrN mulrA -mulNr; congr (_ / _).
rewrite -[4]/(2 * 2)%N mulrnA -mulNrn -[(1 *- 2 *+ 2)]mulr_natl.
rewrite exprMn -mulrA [(1 *- 2)^+ _]expr_prod -big_split /= big_ord_recl /=.
rewrite subr0 mulNr divrr // mulN1r 2!mulrN [LHS]opprK.
rewrite exprS !mulrA [2%:R^-1 * 2%:R]mulVf // mul1r.
rewrite (eq_bigr (fun j => let j' := (nat_of_ord j) in (2 * j + 1)%:R)) /=;
        first last.
  move=> j _; rewrite /bump /=.
  rewrite mulNr -mulrN opprD addrC opprK addnC natrD 2!mulrDr.
  rewrite mulrN divff // mulr1 -{2}addn1 {2}natrD addrA addrK.
  by rewrite natrD natrM.
elim: i => [|i IHi].
  by rewrite expr0 big_ord0 double0 fact0 mulr1.
rewrite big_ord_recr /= exprS -mulrA mulrC mulrA {}IHi.
rewrite doubleS !factS 3!natrM.
rewrite [_ * (i.*2)`!%:R]mulrC mulrA [_ * (i.*2)`!%:R]mulrC -!(mulrA); congr (_ * _).
rewrite mulrC invfM // !mulrA; congr (_ * _).
rewrite mul2n -{2}[i.*2.+1]addn1 [X in X / _]mulrC -mulrA; congr (_ * _).
rewrite -[i.*2.+2]addn1 addSnnS -mul2n -[X in (_ + X)%N]muln1.
rewrite -mulnDr addn1 natrM mulfK //.
by have /charf0P -> := charRat.
Qed.

End GenSeries.

Theorem Cat_rat i : ((C i)%:R = i.*2`!%:R / i`!%:R /i.+1`!%:R :> Rat)%R.
Proof.
have Hi := ltnSn i.
by rewrite -(coefFC Hi) coef_trpoly_of_fun (ltnW Hi).
Qed.

Theorem Cat i : C i * i`! * i.+1`! = i.*2`!.
Proof.
have:= Cat_rat i.
move/(congr1 (fun x => x * (i.+1)`!%:R * i`!%:R)%R).
rewrite divrK // divrK // -!natrM => /eqP.
rewrite Num.Theory.eqr_nat => /eqP <-.
by rewrite -[RHS]mulnA [_`! * i`!]mulnC mulnA.
Qed.

End Catalan.

