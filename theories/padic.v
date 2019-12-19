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
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar invlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Open Scope ring_scope.
Import GRing.Theory.

Section DivCompl.
Open Scope nat_scope.

Lemma modB m n d : 0 < d -> d %| m -> n <= m -> m - n = d - n %% d %[mod d].
Proof.
move=> Hd; rewrite (modn_def n d); case: (edivnP n d) => q r ->.
rewrite Hd /= => rled ddivm Hqr.
rewrite subnDA; apply/eqP. rewrite -(eqn_modDr r); apply/eqP.
rewrite [in RHS]subnK ?modnn; last exact: ltnW.
rewrite subnK; first last.
  by rewrite -(leq_add2l (q * d)) subnKC // (leq_trans _ Hqr) // leq_addr.
move: ddivm => /dvdnP [k ->{m Hqr}].
by rewrite -mulnBl modnMl.
Qed.

Definition Zmn m n : 'Z_n -> 'Z_m := fun i => inZp i.

Variables m n p : nat.
Hypothesis (mgt1 : m > 1) (ngt1 : n > 1).
Hypothesis (mdivn : m %| n).
Lemma Zmn_is_rmorphism : rmorphism (@Zmn m n).
Proof.
repeat split=> [[i Hi] [j Hj]|]; rewrite /= /Zmn /inZp;
    apply val_inj; move: Hi Hj; rewrite /= !Zp_cast // => Hi Hj.
- rewrite !modnDml !modnDmr modn_dvdm //.
  by apply/eqP; rewrite eqn_modDl modB //; apply: ltnW.
- by rewrite modn_dvdm // modnMml modnMmr.
Qed.

Lemma comp_Zmn : @Zmn m n \o @Zmn n p =1 @Zmn m p.
Proof.
move=> i /=; apply val_inj => /=.
rewrite (Zp_cast ngt1) (Zp_cast mgt1).
rewrite (modn_def i n); case: (edivnP i n) => {i} q r -> /= Hr.
by move: mdivn => /dvdnP [k ->]; rewrite mulnA -modnDml modnMl add0n.
Qed.

End DivCompl.

Definition padic_bond (p : nat) of (prime p) :=
  fun (i j : nat) of (i <= j)%O => @Zmn (p ^ i.+1)%N (p ^ j.+1)%N.

Section PadicInvSys.

Variable (p : nat).
Local Notation Z j := 'Z_(p ^ j.+1).

Hypothesis (p_pr : prime p).
Lemma expgt1 l : (1 < p ^ (l.+1))%N.
Proof.
apply: (leq_trans (prime_gt1 p_pr)).
by rewrite -{1}(expn1 p) leq_exp2l // prime_gt1.
Qed.
Lemma expgt0 l : (0 < p ^ (l.+1))%N.
Proof. exact: ltn_trans _ (expgt1 l). Qed.

Lemma truncexp l : (Zp_trunc (p ^ l.+1)).+2 = (p ^ l.+1)%N.
Proof. by rewrite Zp_cast // expgt1. Qed.

Lemma expN1lt n : (p ^ n.+1 - 1 < p ^ n.+1)%N.
Proof.
have:= expgt1 n; case: (p ^ _)%N => // k _.
by rewrite subSS subn0 ltnS.
Qed.

Local Lemma expdiv n i j : (i <= j)%O -> (n ^ i.+1 %| n ^ j.+1)%N.
Proof.
rewrite leEnat -ltnS => Hij;
by rewrite -(subnK Hij) expnD dvdn_mull.
Qed.

Program Definition padic_invsys :=
  InvSys (bonding := fun (i j : nat) (H : (i <= j)%O) => padic_bond p_pr H)
         0%N _ _.
Next Obligation. by move=> x; apply valZpK. Qed.
Next Obligation. exact: comp_Zmn (expgt1 i) (expgt1 j) (expdiv _ _). Qed.

Variables (i j : nat) (H : (i <= j)%O).
Lemma bond_is_rmorphism : rmorphism (padic_bond p_pr H).
Proof. exact: Zmn_is_rmorphism (expgt1 i) (expgt1 j) (expdiv _ _). Qed.
Canonical bond_additive := Additive bond_is_rmorphism.
Canonical bond_rmorphism := RMorphism bond_is_rmorphism.

End PadicInvSys.


Section Defs.

Variables (p : nat) (p_pr : prime p).

Definition padic_int := {invlim padic_invsys p_pr}.
Canonical padic_int_eqType := EqType padic_int gen_eqMixin.
Canonical padic_int_choiceType := ChoiceType padic_int gen_choiceMixin.
Canonical padic_int_invlimType :=
  InvLimType padic_int (invlim_Mixin (padic_invsys p_pr)).
Canonical padic_int_zmodType :=
  Eval hnf in ZmodType padic_int [zmodMixin of padic_int by <-].
Canonical padic_int_ringType :=
  Eval hnf in RingType padic_int [ringMixin of padic_int by <-].
Canonical padic_int_comRingType :=
  Eval hnf in ComRingType padic_int [comRingMixin of padic_int by <-].
Canonical padic_int_unitRingType :=
  Eval hnf in UnitRingType padic_int [unitRingMixin of padic_int by <-].
Canonical padic_intp_comUnitRingType := [comUnitRingType of padic_int].

End Defs.


Section PadicTheory.

Variables (p : nat) (p_pr : prime p).
Implicit Type x y : padic_int p_pr.

Lemma padic_unit x : (x \is a GRing.unit) = ('pi_0%N x != 0).
Proof.
apply/forallbP/idP => [/(_ 0%N) | /= Hx i].
- by apply/memPn: ('pi_0%N x); rewrite unitr0.
- have:= leq0n i; rewrite -leEnat => Hi.
  move: (ilprojE x Hi) Hx; rewrite {Hi} /padic_bond /Zmn => <-.
  move: ('pi_i x); rewrite {x} expn1 -(pdiv_id p_pr) => m /=.
  rewrite -{2}(natr_Zp m) unitZpE ?expgt1 ?pdiv_id //.
  rewrite /inZp /= -(natr_Zp (Ordinal _)) /= -unitfE unitFpE //.
  rewrite pdiv_id // in m |- *.
  rewrite (@Zp_cast p) ?prime_gt1 // coprime_modr.
  exact: coprime_expl.
Qed.

Fact padic_mul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
case: (altP (x =P 0)) => //= /il_neq0 [/= i Hneq0] Hxy.
apply/eqP/invlimE=> /= j.
move: Hxy => /(congr1 'pi_(i+j)%N); rewrite raddf0 rmorphM /=.
move: Hneq0.
have:= leq_addr i j; rewrite -leEnat => Hij; rewrite -(ilprojE y Hij).
have:= leq_addr j i; rewrite -leEnat => Hji; rewrite -(ilprojE x Hji).
rewrite /padic_bond /Zmn {Hij Hji} [(j + i)%N]addnC.
move: ('pi_(i + j)%N x) ('pi_(i + j)%N y) => {x y} [x Hx] [y Hy].
rewrite /inZp /= -(natr_Zp (Ordinal _)) /=.
rewrite truncexp // (Zp_nat_mod (expgt1 p_pr i)) => xmod.
have {}xmod : (x %% p^(i.+1) != 0)%N.
  move: xmod; apply contra => /eqP Heq.
  by rewrite Zp_nat; apply/eqP/val_inj; rewrite /= truncexp.
move=> /(congr1 val); rewrite /= (truncexp p_pr (i + j)) => /eqP xymod.
apply val_inj; rewrite /= {1}truncexp // => {Hx Hy}.
have xn0 : (0 < x)%N.
  by apply/contraR: xmod; rewrite -leqNgt leqn0 => /eqP ->; rewrite mod0n.
case: (ltnP 0%N y)=> [yn0|]; first last.
  rewrite leqn0 => /eqP ->; rewrite mod0n.
  (** TODO: rewrite raddd0. should be sufficient *)
  by rewrite (raddf0 (ilproj_additive [invLimType of padic_int p_pr] j)).
have xyn0 : (0 < x * y)%N by rewrite muln_gt0 xn0 yn0.
(** TODO: rewrite raddd0. should be sufficient *)
rewrite (raddf0 (ilproj_additive [invLimType of padic_int p_pr] j)).
apply/eqP; rewrite -/(dvdn _ _) pfactor_dvdn //.
move: xymod; rewrite -/(dvdn _ _) pfactor_dvdn // lognM //.
move: xmod;  rewrite -/(dvdn _ _) pfactor_dvdn // -leqNgt => logx.
by apply contraLR; rewrite -!leqNgt; exact: leq_add.
Qed.
Canonical padic_int_idomainType :=
  Eval hnf in IdomainType (padic_int p_pr) padic_mul_eq0.

End PadicTheory.



Section Tests.
Variables (p : nat) (p_pr : prime p).

Fact padicN1_thread :
  isthread (padic_invsys p_pr) (fun n => inord (p ^ n.+1 - 1)).
Proof.
move=> m n mlen /=; rewrite /padic_bond /Zmn; apply val_inj => /=.
rewrite !inordK truncexp // ?expN1lt //.
rewrite modB; try exact: expgt0; try exact: expdiv.
by rewrite (modn_small (expgt1 _ _)) // modn_small // expN1lt.
Qed.
Definition ZpN1 : padic_int p_pr := MkInvLim padicN1_thread.

Lemma ZpN1E : ZpN1 = -1.
Proof.
apply/invlimE => /= n; rewrite rmorphN rmorph1; apply val_inj => /=.
rewrite inordK ?truncexp // ?expN1lt //.
by rewrite (modn_small (expgt1 _ _)) // modn_small // expN1lt.
Qed.

End Tests.
