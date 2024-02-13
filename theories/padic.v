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
- [Zmn m n]    == the morphism from \(\mathbb{Z}/n\mathbb{Z}\) to
                  \(\mathbb{Z}/m\mathbb{Z}\) assuming [m] divide [n].

In what follows we assume that [p] is a prime number with [p_pr : prime p].
- [padic_bond p_pr (H :i <= j)] the morphism \(\mathbb{Z}/p^j\mathbb{Z}\)
                  to \(\mathbb{Z}/p^i\mathbb{Z}\).
- [padic_invsys p_pr] == the \(p\)-adic inverse system:
#
\[\dots \mapsto \mathbb{Z}/p^{n+1}\mathbb{Z} \mapsto \mathbb{Z}/p^{n}\mathbb{Z}
\mapsto\dots\mapsto  \mathbb{Z}/p^2\mathbb{Z} \mapsto \mathbb{Z}/p\mathbb{Z}\,.
\]
#

- [padic_int p_pr] == the \(p\)-adic integers ring [Zp] constructed as the
                  inverse limit of [padic_invsys p_pr]. It is equiped with
                  [idomainType] and [comUnitRingInvLimType (padic_invsys p_pr)]
                  canonical structures.
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
Hypothesis (p_pr : prime p).


Lemma primeX_gt0 l : (0 < p ^ l)%N.
Proof. by rewrite expn_gt0 prime_gt0. Qed.
Lemma primeX_gt1 l : (1 < p ^ (l.+1))%N.
Proof.
apply: (leq_trans (prime_gt1 p_pr)).
by rewrite -{1}(expn1 p) leq_exp2l // prime_gt1.
Qed.
Hint Resolve primeX_gt0 primeX_gt1 : core.

Lemma ZpX_cast l : (Zp_trunc (p ^ l.+1)).+2 = (p ^ l.+1)%N.
Proof. by rewrite Zp_cast. Qed.

Lemma expN1lt n : (p ^ n.+1 - 1 < p ^ n.+1)%N.
Proof.
have:= primeX_gt1 n; case: (p ^ _)%N => // k _.
by rewrite subSS subn0 ltnS.
Qed.

Lemma dvdnX n i j : (i <= j)%N -> (n ^ i %| n ^ j)%N.
Proof. by move=> /subnK <-; rewrite expnD dvdn_mull. Qed.

Fact padic_bond_id i (Hii : (i <= i)%O) : padic_bond p_pr Hii =1 id.
Proof. by move=> x; apply valZpK. Qed.
Fact padic_bond_trans i j k (Hij : (i <= j)%O) (Hjk : (j <= k)%O) :
  padic_bond p_pr Hij \o padic_bond p_pr Hjk
  =1 padic_bond p_pr (le_trans Hij Hjk).
Proof. exact/comp_Zmn/dvdnX. Qed.
Definition padic_invsys :=
  IsInvSys (bonding := fun (i j : nat) (H : (i <= j)%O) => padic_bond p_pr H)
         0%N padic_bond_id padic_bond_trans.
Definition padic_int := {invlim padic_invsys}.

Variables (i j : nat) (H : (i <= j)%O).

Fact bond_is_additive : additive (padic_bond p_pr H).
Proof. exact/Zmn_is_additive/dvdnX. Qed.
HB.instance Definition _ :=
  GRing.isAdditive.Build ('Z_(p ^ j.+1)) ('Z_(p ^ i.+1)) _  bond_is_additive.

Fact bond_is_multiplicative : multiplicative (padic_bond p_pr H).
Proof. exact/Zmn_is_multiplicative/dvdnX. Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build
    ('Z_(p ^ j.+1)) ('Z_(p ^ i.+1)) _  bond_is_multiplicative.

End PadicInvSys.
#[global] Hint Resolve primeX_gt0 primeX_gt1 : core.


Section PadicTheory.

Variables (p : nat) (p_pr : prime p).
Local Notation Zp := (padic_int p_pr).

Let prime_gt1 := prime_gt1 p_pr.
Let primeX_gt0 := primeX_gt0 p_pr.
Let primeX_gt1 := primeX_gt1 p_pr.

Implicit Types (x y : padic_int p_pr) (i j n : nat).

Lemma nat_padic0E (n : nat) : (n%:~R == 0 :> Zp) = (n == 0%N).
Proof.
apply/eqP/eqP => [|-> //] H.
move/(congr1 'pi_n): H; rewrite raddf0 rmorph_nat Zp_nat.
move/(congr1 \val) => /= <-; rewrite modn_small //.
by rewrite ZpX_cast // (ltnW (ltn_expl n.+1 _)).
Qed.
Lemma int_padic0E (z : int) : (z%:~R == 0 :> Zp) = (z == 0%N).
Proof.
apply/idP/idP => [| /eqP-> //].
case: (intP z) => // n; first by rewrite nat_padic0E.
by rewrite raddfN /= !oppr_eq0 nat_padic0E.
Qed.
Lemma int_padic_inj : injective (intr : int -> Zp).
Proof.
by move=> i j /eqP; rewrite -subr_eq0 -rmorphB /= int_padic0E subr_eq0 => /eqP.
Qed.
Lemma nat_padic_inj : injective (intr : nat -> Zp).
Proof.
have /eq_inj : intr \o Posz =1 (intr : nat -> Zp) by [].
by apply; apply (inj_comp int_padic_inj) => i j /eqP/[!eqz_nat]/eqP.
Qed.

Lemma padicp_nat i n : 'pi[Zp]_n i%:~R = (i %% p ^ n.+1)%N :> nat.
Proof. by rewrite rmorph_nat /= Zp_nat /= ZpX_cast. Qed.

Local Lemma proj_pXn n : 'pi[Zp]_n (p%:~R ^ n.+1) = 0.
Proof. by apply val_inj; rewrite -exprnP -natrX /= padicp_nat modnn. Qed.

Lemma valuat_nat_padic n : (n > 0)%N -> valuat (n%:~R : Zp) = Nat (logn p n).
Proof.
move/(pfactor_coprime p_pr) => [r copr {1}->]; move: (logn _ _) => {}n.
apply valuatNatE => [| i ltin].
  rewrite -val_eqE /= padicp_nat expnS.
  rewrite -muln_modl muln_eq0 negb_or -[X in _ && X]lt0n primeX_gt0 // andbT.
  by rewrite -/(dvdn _ _) -prime_coprime.
apply/eqP; rewrite -val_eqE /= padicp_nat.
by rewrite -(subnK ltin) expnD mulnA modnMl.
Qed.

Fact div_pXn_subproof n x :
  isthread (padic_invsys p_pr)
           (fun i => inZp (('pi_(i + n) x) %/ p ^ n)%N).
Proof.
move => i j leij.
have leijn1 : (i + n <= j + n)%O by rewrite leEnat leq_add2r -leEnat.
rewrite -(ilprojE x leijn1) /padic_bond /= /Zmn; apply val_inj => /=.
move: (val _) => y; rewrite !ZpX_cast //.
rewrite !modn_dvdm ?dvdnX // !modn_divl -expnD.
by rewrite modn_dvdm // dvdnX.
Qed.
Definition div_pXn n x : Zp := ilthr (div_pXn_subproof n x).

Lemma mul_pXnK n : cancel ( *%R (p%:~R ^ n) ) (div_pXn n).
Proof.
move=> /= x; apply/invlimE => /= i; rewrite ilthrP.
have -> : (p%:~R ^ n) = (p ^ n)%N%:~R :> Zp by rewrite !rmorphXn /=.
rewrite !rmorphM rmorph_nat /=.
have lei_in : (i <= (i + n)%N)%O by rewrite leEnat leq_addr.
rewrite -(ilprojE x lei_in) /= /padic_bond /Zmn; apply val_inj => /=.
move: (val ('pi_(i + n)%N x)) => {}x.
rewrite val_Zp_nat // [(p ^ n %% _)%N]modn_small; first last.
  by rewrite ltn_exp2l // ltnS leq_addl.
rewrite !ZpX_cast // -addSn divn_modl; last exact/dvdnX/leq_addl.
by rewrite mulKn // expnD mulnK // modn_mod.
Qed.

Lemma div_pXnK x n :
  'pi_n x = 0 -> p%:~R ^ n.+1 * (div_pXn n.+1 x) = x.
Proof.
move=> pin0.
have {pin0} div_pix i : (p ^ n.+1 %| 'pi_(i + n.+1)%N x)%N.
  have len_in : (n <= (i.+1 + n)%N)%O by rewrite leEnat leq_addl.
  have:= ilprojE x len_in; rewrite {}pin0 => /(congr1 val)/= /[!addSnnS].
  by move: (val _) => {}x; rewrite ZpX_cast // /dvdn => ->.
apply/invlimE => /= i.
rewrite rmorphM rmorphXn rmorph_nat /= ilthrP.
have lei_in : (i <= (i + n.+1)%N)%O by rewrite leEnat leq_addr.
rewrite -(ilprojE x lei_in) /= /padic_bond /Zmn.
move/(_ i): div_pix => /dvdnP[k ->].
rewrite -[RHS]Zp_nat natrM !rmorphXn mulrC; congr (_ * _).
by rewrite mulnK // Zp_nat.
Qed.

Lemma padicp_eq0 x n : 'pi_n x = 0 -> {t : Zp | x = p%:~R ^ n.+1 * t}.
Proof. by move=> /div_pXnK <-; exists (div_pXn n.+1 x). Qed.

Lemma padicp_MpXn_eq0 x n : ('pi_n (p%:~R ^ n * x) == 0) = ('pi_0%N x == 0).
Proof.
apply/eqP/eqP.
  move/padicp_eq0 => [y] /(congr1 (div_pXn n)).
  rewrite exprSzr -mulrA !mul_pXnK => ->.
  by rewrite rmorphM /= proj_pXn mul0r.
move/padicp_eq0 => [y /[!expr1z] ->{x}].
by rewrite mulrA -exprSzr rmorphM /= proj_pXn mul0r.
Qed.

Variant valuat_padic_spec x : natbar -> Type :=
  | ValPadicNat n t of 'pi_n x != 0
    & x = p%:~R ^+ n * t : valuat_padic_spec x (Nat n)
  | ValPadicInf of x = 0 : valuat_padic_spec x Inf.

Lemma valuatXnP x : valuat_padic_spec x (valuat x).
Proof.
case: valuatP => [[|v] Hv vmin /= |->]; last exact: ValPadicInf.
  by apply: ValPadicNat; rewrite // expr0 mul1r.
move/(_ _ (ltnSn v)): vmin => /padicp_eq0[t Hx].
exact: (ValPadicNat (t := t)).
Qed.

Lemma valuatM x y : valuat (x * y) = valuat x + valuat y.
Proof.
have [/= vx a pix eqx | ->] := valuatXnP x; last by rewrite mul0r valuat0.
have [/= vy b piy eqy | ->] := valuatXnP y; last by rewrite mulr0 valuat0.
rewrite -raddfD /=; apply valuatNatE.
  move: pix piy; rewrite {x}eqx {y}eqy mulrACA -exprD !padicp_MpXn_eq0 {vx vy}.
  rewrite rmorphM /=; move: (_ a) (_ b) => {}a {}b.
  (* Fixed bad mathcomp statement *)
  have Fp_Zcast : Zp_trunc (pdiv p) = Zp_trunc p by have[]:= Fp_Zcast p_pr.
  rewrite expn1 -Fp_Zcast in a b |- *.
  exact: mulf_neq0.
rewrite natrE=> i lti.
rewrite eqx eqy mulrACA -exprD -(subnK lti) exprD !mulrA !rmorphM /=.
by rewrite proj_pXn !(mulr0, mul0r).
Qed.

(** ** The p-adic integers is an integral domain *)
Lemma padic_unit x : (x \is a GRing.unit) = ('pi_0%N x != 0).
Proof.
apply/ilunitP/idP  => [/(_ 0%N) | /= Hx i].
- by apply/memPn: ('pi_0%N x); rewrite unitr0.
- have:= leq0n i; rewrite -leEnat => Hi.
  move: (ilprojE x Hi) Hx; rewrite /= {Hi} /padic_bond /Zmn => <-.
  move: ('pi_i x); rewrite {x} expn1 -(pdiv_id p_pr) => /= m.
  rewrite -{2}(natr_Zp m) unitZpE ?pdiv_id //.
  rewrite /inZp /= -(natr_Zp (Ordinal _)) /= -unitfE unitFpE //.
  rewrite pdiv_id ?(@Zp_cast p) // in m |- *.
  by rewrite coprime_modr; apply: coprimeXl.
Qed.

Lemma padic_unit_valuat x : (x \is a GRing.unit) = (valuat x == Nat 0).
Proof. by rewrite padic_unit valuat_eq0P. Qed.

Fact padic_mul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof. by move/eqP; rewrite -!valuat0P valuatM addbar_eqI. Qed.
HB.instance Definition _ :=
  GRing.ComUnitRing_isIntegral.Build (padic_int p_pr) padic_mul_eq0.

End PadicTheory.


Section Tests.
Variables (p : nat) (p_pr : prime p).

Fact padicN1_thread :
  isthread (padic_invsys p_pr) (fun n => inord (p ^ n.+1 - 1)).
Proof.
move=> m n mlen /=; rewrite /padic_bond /Zmn; apply val_inj => /=.
rewrite !inordK ZpX_cast // ?expN1lt //.
rewrite modB; try exact: primeX_gt0; try exact: dvdnX.
by rewrite (modn_small (primeX_gt1 _ _)) // modn_small // expN1lt.
Qed.
Definition ZpN1 : padic_int p_pr := ilthr padicN1_thread.

Lemma ZpN1E : ZpN1 = -1.
Proof.
apply/invlimE => /= n; rewrite rmorphN rmorph1 ilthrP.
apply val_inj; rewrite /= inordK ?ZpX_cast // ?expN1lt //.
by rewrite (modn_small (primeX_gt1 _ _)) // modn_small // expN1lt.
Qed.

End Tests.
