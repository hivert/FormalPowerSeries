(** * Combi.padic : padic integer *)
(******************************************************************************)
(*       Copyright (C) 2019-2021 Florent Hivert <florent.hivert@lri.fr>       *)
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
(** #
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
 # *)
(** * The ring of p-adic integers

We define the following:
- [Zmn m n]      == the morphism from \(Z/nZ\) to \(Z/mZ\) assuming [m] divide [n].
- [padic_invsys] == the \(p\)-adic inverse system.
- [padic_int Pf] == the \(p\)-adic integers ring [Zp] where [Pf] is a proof that
                    [p] is a prime number. It is equiped with a [idomainType]
                    and [comUnitRingInvLimType padic_invsys] structure.
*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar directed invlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Open Scope ring_scope.
Import GRing.Theory.

(** ** The p-adic inverse system *)
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

Lemma Zmn_is_additive : additive (@Zmn m n).
Proof.
move=> /= [i Hi] [j Hj]; rewrite /= /Zmn /inZp.
apply val_inj; move: Hi Hj; rewrite /= !Zp_cast // => Hi Hj.
rewrite !modnDml !modnDmr modn_dvdm //.
by apply/eqP; rewrite eqn_modDl modB //; apply: ltnW.
Qed.

Lemma Zmn_is_multiplicative : multiplicative (@Zmn m n).
Proof.
split => [[i Hi] [j Hj]|]; rewrite /= /Zmn /inZp //.
apply val_inj; move: Hi Hj; rewrite /= !Zp_cast // => Hi Hj.
by rewrite modn_dvdm // modnMml modnMmr.
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

Lemma expdiv n i j : (i <= j)%O -> (n ^ i.+1 %| n ^ j.+1)%N.
Proof.
rewrite leEnat -ltnS => Hij;
by rewrite -(subnK Hij) expnD dvdn_mull.
Qed.

Fact padic_bond_id i (Hii : (i <= i)%O) : padic_bond p_pr Hii =1 id.
Proof. by move=> x; apply valZpK. Qed.
Fact padic_bond_trans i j k (Hij : (i <= j)%O) (Hjk : (j <= k)%O) :
  padic_bond p_pr Hij \o padic_bond p_pr Hjk
  =1 padic_bond p_pr (le_trans Hij Hjk).
Proof. exact: comp_Zmn (expgt1 i) (expgt1 j) (expdiv _ _). Qed.
Definition padic_invsys :=
  InvSys (bonding := fun (i j : nat) (H : (i <= j)%O) => padic_bond p_pr H)
         0%N padic_bond_id padic_bond_trans.

Variables (i j : nat) (H : (i <= j)%O).

Fact bond_is_additive : additive (padic_bond p_pr H).
Proof. exact: Zmn_is_additive (expgt1 i) (expgt1 j) (expdiv _ _). Qed.
HB.instance Definition _ :=
  GRing.isAdditive.Build (Z j) (Z i) _  bond_is_additive.

Fact bond_is_multiplicative : multiplicative (padic_bond p_pr H).
Proof. exact: Zmn_is_multiplicative (expgt1 i) (expgt1 j) (expdiv _ _). Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build (Z j) (Z i) _  bond_is_multiplicative.

End PadicInvSys.


(** ** The p-adic integers integral domain *)
Definition padic_int (p : nat) (p_pr : prime p) := {invlim padic_invsys p_pr}.

Section PadicTheory.

Variables (p : nat) (p_pr : prime p).
Implicit Type x y : padic_int p_pr.

Lemma padic_unit x : (x \is a GRing.unit) = ('pi_0%N x != 0).
Proof.
apply/asboolP/idP => [/(_ 0%N) | /= Hx i].
- by apply/memPn: ('pi_0%N x); rewrite unitr0.
- have:= leq0n i; rewrite -leEnat => Hi.
  move: (ilprojE x Hi) Hx; rewrite {Hi} /padic_bond /Zmn => <-.
  move: ('pi_i x); rewrite {x} expn1 -(pdiv_id p_pr) => /= m.
  rewrite -{2}(natr_Zp m) unitZpE ?expgt1 ?pdiv_id //.
  rewrite /inZp /= -(natr_Zp (Ordinal _)) /= -unitfE unitFpE //.
  rewrite pdiv_id ?(@Zp_cast p) ?prime_gt1 // in m |- *.
  by rewrite coprime_modr; apply: coprimeXl.
Qed.

Fact padic_mul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
case: (altP (x =P 0)) => //= /il_neq0 [/= i Hneq0] Hxy.
apply/eqP/invlimE=> /= j.
move: Hxy => /(congr1 'pi_(i+j)%N); rewrite !raddf0 rmorphM /=.
move: Hneq0.
have:= leq_addl i j; rewrite -leEnat => Hij; rewrite -(ilprojE y Hij).
have:= leq_addr j i; rewrite -leEnat => Hji; rewrite -(ilprojE x Hji).
rewrite /padic_bond /Zmn {Hij Hji}.
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
  by rewrite leqn0 => /eqP ->; rewrite mod0n.
have xyn0 : (0 < x * y)%N by rewrite muln_gt0 xn0 yn0.
apply/eqP; rewrite -/(dvdn _ _) pfactor_dvdn //.
move: xymod; rewrite -/(dvdn _ _) pfactor_dvdn // lognM //.
move: xmod;  rewrite -/(dvdn _ _) pfactor_dvdn // -leqNgt => logx.
by apply contraLR; rewrite -!leqNgt; exact: leq_add.
Qed.

HB.instance Definition _ := GRing.ComUnitRing.on (padic_int p_pr).
HB.instance Definition _ :=
  GRing.ComUnitRing_isIntegral.Build (padic_int p_pr) padic_mul_eq0.

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
Definition ZpN1 : padic_int p_pr := ilthr padicN1_thread.

Lemma ZpN1E : ZpN1 = -1.
Proof.
apply/invlimE => /= n; rewrite rmorphN rmorph1 ilthrP.
apply val_inj; rewrite /= inordK ?truncexp // ?expN1lt //.
by rewrite (modn_small (expgt1 _ _)) // modn_small // expN1lt.
Qed.

End Tests.
