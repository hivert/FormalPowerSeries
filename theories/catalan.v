(** Catalan number via generating functions *)
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
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype div bigop ssralg poly binomial rat ssrnum.

Require Import tfps auxresults.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Catalan.

Variable (C : nat -> nat).

Hypothesis C0 : C 0 = 1%N.
Hypothesis CS : forall n : nat, C n.+1 = \sum_(i < n.+1) C i * C (n - i).

Local Definition Csimpl := (C0, CS, big_ord0, big_ord_recl).
Example C1 : C 1 = 1.  Proof. by rewrite !Csimpl. Qed.
Example C2 : C 2 = 2.  Proof. by rewrite !Csimpl. Qed.
Example C3 : C 3 = 5.  Proof. by rewrite !Csimpl. Qed.
Example C4 : C 4 = 14. Proof. by rewrite !Csimpl. Qed.
Example C5 : C 5 = 42. Proof. by rewrite !Csimpl. Qed.

Import GRing.Theory.

Local Definition Rat := [fieldType of rat].
Local Definition char_Rat := Num.Theory.char_num [numDomainType of Rat].
Local Definition nat_unit := nat_unit_field char_Rat.
Local Definition fact_unit := fact_unit char_Rat.
Hint Resolve char_Rat nat_unit : core.

Section GenSeries.

Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Variable n : nat.
Definition FC : {tfps Rat n} := [tfps i => (C i)%:R].

Lemma FC_in_coef0_eq1 : FC \in coeft0_eq1.
Proof. by rewrite coeft0_eq1E coef_tfps_of_fun C0. Qed.

Proposition FC_algebraic_eq : FC = 1 + \X * FC ^+ 2.
Proof.
rewrite /FC; apply/tfpsP => i le_in.
rewrite coef_tfps_of_fun coefD coef1 coef_tfpsXM le_in.
case: i le_in => [|i] lt_in; first by rewrite C0 addr0.
rewrite add0r CS /= expr2 coef_trXn (ltnW lt_in) coefM natr_sum.
apply eq_bigr => [[j]]; rewrite /= ltnS => le_ji _.
rewrite natrM !coef_poly.
rewrite (leq_trans (leq_ltn_trans le_ji lt_in) (leqnSn _)).
by rewrite ltnS (leq_trans (leq_subr _ _) (ltnW lt_in)).
Qed.

End GenSeries.


(** Extraction of the coefficient using square root and Newton's formula *)
Section AlgebraicSolution.

Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Lemma mulr_nat n i (f : {tfps Rat n}) : i%:R *: f = i%:R * f.
Proof. by rewrite scaler_nat -[f *+ i]mulr_natr mulrC. Qed.

Theorem FC_algebraic_solution n :
  \X * FC n = 2%:R^-1 *: (1 - \sqrt (1 - 4%:R *: \X)).
Proof.
have co1 : 1 - 4%:R *: \X \in @coeft0_eq1 Rat n.
  by rewrite mulr_nat coeft0_eq1E coefD mulrC coefN coef_tfpsXM coef1 subr0.
have: (2%:R *: \X * FC n - 1) ^+ 2 = 1 - 4%:R *: \X.
  apply/eqP; rewrite !mulr_nat sqrrB1 !exprMn 2!expr2 -natrM.
  rewrite mulrA -subr_eq0 opprB [_ - 1]addrC addrA addrK addrC addrA.
  rewrite -{1}(mulr1 (4%:R * _)) -[X in _ + X + _]mulrA -mulrDr.
  rewrite -FC_algebraic_eq.
  by rewrite -[_ *+ 2]mulr_natl !mulrA -natrM subrr.
move/(sqrtE char_Rat) => /(_ co1) [HeqP | HeqN].
  exfalso; move: HeqP => /(congr1 (fun x : {tfps _ _ } => x`_0)).
  rewrite mulr_nat coefB -mulrA mulrC -mulrA coef_tfpsXM coef1.
  rewrite (eqP (coeft0_eq1_expr _ _)) /= => /eqP.
  rewrite -subr_eq0 add0r -oppr_eq0 opprD opprK -mulr2n => /eqP Habs.
  by have:= char_Rat 2; rewrite !inE Habs /= eq_refl.
have neq20 : 2%:R != 0 :> Rat by rewrite Num.Theory.pnatr_eq0.
apply (scalerI neq20); rewrite scalerA divff // scale1r -HeqN.
by rewrite addrC subrK scalerAl.
Qed.

Theorem coefFC n i : (i < n)%N -> (FC n)`_i = i.*2`!%:R / i`!%:R /i.+1`!%:R.
Proof.
move=> Hi.
have:= congr1 (fun x : {tfps _ _ } => x`_i.+1) (FC_algebraic_solution n).
rewrite coef_tfpsXM Hi ![X in (X = _)]/= => ->.
rewrite coefZ coefB coef1 sub0r -scaleNr coef_expr1cX ?{}Hi //.
rewrite mulrN mulrA -mulNr; congr (_ / (i.+1)`!%:R).
rewrite -[4]/(2 * 2)%N mulrnA -mulNrn -[(1 *- 2 *+ 2)]mulr_natl.
rewrite exprMn -mulrA.
have -> : (1 *- 2)^+ i.+1 = \prod_(i0 < i.+1) (1 *- 2) :> rat.
  by rewrite prodr_const /= card_ord.
rewrite -big_split /= big_ord_recl /=.
rewrite subr0 mulNr divrr // mulN1r 2!mulrN [LHS]opprK.
rewrite exprS !mulrA [2%:R^-1 * 2%:R]mulVf // mul1r.
rewrite (eq_bigr (fun j : 'I_i => (2 * j + 1)%:R)) /=; last first.
  move=> j _; rewrite /bump /=.
  rewrite mulNr -mulrN opprD addrC opprK addnC natrD 2!mulrDr.
  rewrite mulrN divff // mulr1 -{2}addn1 {2}natrD addrA addrK.
  by rewrite natrD natrM.
elim: i => [|i IHi]; first by rewrite expr0 big_ord0 double0 fact0 mulr1.
rewrite big_ord_recr /= exprS -mulrA mulrC mulrA {}IHi.
rewrite doubleS !factS 3!natrM.
set F := (i.*2)`!%:R; rewrite [_ * F]mulrC mulrA [_ * F]mulrC -!mulrA.
congr (_ * _); rewrite {F} mulrC invfM // !mulrA; congr (_ * _).
rewrite mul2n -{2}[i.*2.+1]addn1 [X in X / _]mulrC -mulrA; congr (_ * _).
rewrite -[i.*2.+2]addn1 addSnnS -mul2n -[X in (_ + X)%N]muln1.
rewrite -mulnDr addn1 natrM mulfK //.
by have /charf0P -> := char_Rat.
Qed.

Theorem Cat_rat i : (C i)%:R = i.*2`!%:R / i`!%:R /i.+1`!%:R :> Rat.
Proof. by rewrite -(coefFC (ltnSn i)) coef_tfps_of_fun (ltnW _). Qed.

Local Close Scope ring_scope.

Theorem CatM i : C i * i`! * i.+1`! = i.*2`!.
Proof.
have:= Cat_rat i.
move/(congr1 (fun x => x * (i.+1)`!%:R * i`!%:R)%R).
rewrite (divrK (fact_unit i.+1)) (divrK (fact_unit i)) // -!natrM => /eqP.
rewrite Num.Theory.eqr_nat => /eqP <-.
by rewrite -[RHS]mulnA [_`! * i`!]mulnC mulnA.
Qed.

Theorem CatV i : C i = i.*2`! %/ (i`! * i.+1`!).
Proof.
have:= CatM i; rewrite -mulnA => /(congr1 (fun j => j %/ (i`! * (i.+1)`!))).
by rewrite mulnK // muln_gt0 !fact_gt0.
Qed.

Theorem Cat i : C i = 'C(i.*2, i) %/ i.+1.
Proof.
case: (ltnP 0 i)=> [Hi|]; last first.
  by rewrite leqn0 => /eqP ->; rewrite C0 bin0 divn1.
rewrite (CatV i) factS [i.+1 * _]mulnC mulnA.
by rewrite -{3}(addnK i i) addnn divnMA bin_factd // double_gt0.
Qed.

End AlgebraicSolution.


(** Extraction of the coefficient using Lagrange inversion formula *)
Section LagrangeSolution.

Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Lemma one_plusX_2_unit n :((1 + \X) ^+ 2 : {tfps Rat n}) \is a GRing.unit.
Proof.
rewrite unit_tfpsE coeft0M coeftD coeft1.
by rewrite coef_tfpsX mulr0 addr0 mulr1.
Qed.

Proposition FC_fixpoint_eq n : (FC n.+1 - 1) = lagrfix ((1 + \X) ^+ 2).
Proof.
apply: (lagrfix_uniq (one_plusX_2_unit _)).
rewrite {1}FC_algebraic_eq -addrA addrC subrK.
rewrite rmorphX rmorphD /= comp_tfps1 comp_tfpsX //; first last.
  rewrite coeft0_eq0E coef_trXn coeftB coeft1.
  by rewrite coef_tfps_of_fun /= C0 subrr.
rewrite -(trXnt1 _ n.+1) raddfB /= addrC subrK -rmorphX /=.
apply/tfpsP => i le_in1.
rewrite coef_tfpsXM coeft_tmulX coef_trXnt.
by case: i le_in1.
Qed.

Theorem CatM_Lagrange i : (i.+1 * (C i))%N = 'C(i.*2, i).
Proof.
case: i => [|i]; first by rewrite C0 mul1n bin0.
apply/eqP; rewrite -(Num.Theory.eqr_nat [numDomainType of Rat]); rewrite natrM.
have:= congr1 (fun s : {tfps Rat i.+1} => s`_i.+1) (FC_fixpoint_eq i).
rewrite coef_tfps coeftD coef_tfps_of_fun ltnSn.
rewrite coeftN coeft1 subr0 /= => ->.
rewrite -/(_`_i.+1) (coeft_lagrfix (nat_unit_field _)) ?one_plusX_2_unit //.
rewrite -exprM mul2n addrC exprD1n coeft_sum.
have Hord : (i < (i.+1).*2.+1)%N.
  by rewrite ltnS doubleS -addnn -!addnS leq_addr.
rewrite (bigD1 (Ordinal Hord)) //= -!/(_`_i.+1).
rewrite coeftMn coef_tfpsXn // eqxx leqnn /= (_ : 1%:R = 1) //.
rewrite big1 ?addr0 => [|[j /= Hj]]; first last.
  rewrite -val_eqE /= => {Hj} /negbTE Hj.
  by rewrite coeftMn coef_tfpsXn eq_sym Hj andbF mul0rn.
rewrite ltnS in Hord.
rewrite -bin_sub // -{2}addnn -addSnnS addnK.
by rewrite mulrA -natrM mul_bin_left -addnn addnK natrM mulrC mulKr.
Qed.

Local Close Scope ring_scope.

Theorem Cat_Lagrange i : C i = 'C(i.*2, i) %/ i.+1.
Proof.
by have:= congr1 (fun m => m %/ i.+1) (CatM_Lagrange i); rewrite mulnC mulnK.
Qed.

End LagrangeSolution.


(** Extraction of the coefficient using Holonomic differential equation *)
Section HolonomicSolution.

Local Open Scope ring_scope.
Local Open Scope tfps_scope.

Proposition FC_differential_eq n :
  (1 - \X *+ 2) * (FC n.+1) + (1 - \X *+ 4) * tmulX (FC n.+1)^`() = 1.
Proof.
have:= FC_algebraic_eq n.+1; move: (FC n.+1) => F Falg.
have X2Fu : (1 - \X *+ 2 * F) \is a GRing.unit.
  rewrite unit_tfpsE coeftB coeft1.
  by rewrite mulrnAl coeftMn coef_tfpsXM.
have FalgN : \X * F ^+ 2 = F - 1.
  by apply/eqP; rewrite eq_sym subr_eq addrC -Falg.
have -> : tmulX F^`() = (F - 1)/(1 - \X *+ 2 * F).
  rewrite -[LHS]divr1; apply/eqP.
  rewrite (eq_divr (tmulX _)) ?unitr1 // ?X2Fu // mulr1.
  have /= /eqP := congr1 ((@tmulX _ _) \o (@deriv_tfps _ _)) Falg.
  rewrite derivD_tfps deriv_tfps1 add0r.
  rewrite derivM_tfps /= deriv_tfpsX mul1r derivX_tfps /= expr1.
  rewrite raddfD /= -trXnt_tmulX // (tmulXE (F ^+ 2)).
  rewrite trXntM // trXnt_trXnt // trXnt_id trXnt_tfpsX.
  rewrite FalgN [X in _ + tmulX X]mulrC -tmulXM.
  rewrite raddfMn /= [X in (tmulX X) *+ 2]mulrC -tmulXM.
  rewrite -(subr_eq _ _ (_ _ * \X)).
  rewrite -mulrnAr -mulrA -{1}(mulr1 (tmulX _)) -mulrBr.
  by rewrite [_ * \X]mulrC mulrnAl mulrnAr.
rewrite mulrA -[X in X + _](mulrK X2Fu) -mulrDl -[RHS]divr1.
apply/eqP; rewrite eq_divr ?unitr1 // mulr1 mul1r.
rewrite -mulrA [F * _]mulrC [(1 - _ * F) * F]mulrBl -mulrA -expr2.
rewrite mul1r mulrnAl FalgN.
rewrite !mulrnBl opprB addrA (mulr2n F) (opprD F) addrA.
rewrite [_ - F]addrC 2!addrA [-F + _]addrC subrr add0r.
rewrite !mulrBr mulr1 addrA addrC !addrA.
rewrite opprB mulrBl mul1r mulr_natr -mulrnA -[(2 * 2)%N]/4.
rewrite [\X *+ 4 - 1 + _]addrC addrA subrK addrK.
rewrite -addrA -mulNr -mulrDl.
rewrite opprD [-1 + _]addrC addrA subrK -opprD mulNr.
rewrite -[4]/(2 + 2)%N mulrnDr addrA.
by rewrite [_ *- _ + _]addrC subrK.
Qed.

Local Close Scope ring_scope.
Local Close Scope tfps_scope.

Proposition Catalan_rec n : n.+2 * C (n.+1) = (4 * n + 2) * C n.
Proof.
have := congr1 (fun x : {tfps _ _} => (x`_n.+1)%R) (FC_differential_eq n).
rewrite coef1 coeftD !mulrDl !mul1r !coeftD.
rewrite -!mulNrn !(mulrnAl, coeftMn, mulNr, coeftN).
rewrite !coef_tfpsXM coeft_tmulX !coef_deriv_tfps !coef_tfps_of_fun /=.
rewrite ltnSn leqnSn /= ltnS leq_pred.
case: n => [|n] /=; first by rewrite !Csimpl.
move: {n} n.+1 => n; move: (C n.+1) (C n) => Cn1 Cn.
rewrite !mulNrn addrA [X in (X - _)%R]addrC addrA -mulrSr -!mulrnA.
move/eqP; rewrite subr_eq add0r subr_eq -natrD Num.Theory.eqr_nat => /eqP.
rewrite mulnC -mulnDr => ->.
by rewrite mulnC [n * 4]mulnC.
Qed.

Theorem CatM_from_rec n : n.+1 * C n = 'C(n.*2, n).
Proof.
elim: n => [| n IHn] /=; first by rewrite C0 bin0.
rewrite Catalan_rec doubleS !binS.
have leq_n2 : n <= n.*2 by rewrite -addnn leq_addr.
rewrite -[X in _ + _ + X]bin_sub; last exact: (leq_trans leq_n2 (leqnSn _)).
rewrite subSn // -{4}addnn addnK binS addnn.
rewrite addn2 -[4]/(2 * 2) -mulnA !mul2n -doubleS -doubleMl; congr _.*2.
rewrite -IHn -{1}addnn -addnS mulnDl; congr (_ + _).
have:= mul_bin_down n.*2 n.
rewrite mul_bin_diag -{2}addnn addnK -{}IHn mulnA [n * n.+1]mulnC.
rewrite -mulnA ![n.+1 * _]mulnC => /(congr1 (fun m => m %/ n.+1)).
by rewrite !mulnK.
Qed.

Theorem Cat_from_rec i : C i = 'C(i.*2, i) %/ i.+1.
Proof.
by have:= congr1 (fun m => m %/ i.+1) (CatM_from_rec i); rewrite mulnC mulnK.
Qed.

End HolonomicSolution.

End Catalan.
