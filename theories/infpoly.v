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
From SsrMultinomials Require Import ssrcomplements freeg mpoly.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar invlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Def.
Import Order.Syntax.
Import Order.Theory.

Open Scope ring_scope.
Import GRing.Theory.


Section CNVars.

Variable R : comRingType.

Section Defs.

Variable (n m : nat).
Lemma cnvar_tupleP (T : eqType) (t : seq T) (c : T) :
  size (take m t ++ nseq (m - size t) c) == m.
Proof.
rewrite size_cat size_take size_nseq -/(minn _ _) minnC /minn.
case: ltnP => [/ltnW/subnKC -> //|]; rewrite -subn_eq0 => /eqP ->.
by rewrite addn0.
Qed.
Definition cnvar_tuple : m.-tuple {mpoly R[n]} :=
  Tuple (cnvar_tupleP [tuple 'X_i | i < n] 0).
Definition cnvar p := p \mPo cnvar_tuple.

Fact cnvar_is_rmorphism : rmorphism cnvar.
Proof. repeat split; [exact: rmorphB | exact: rmorphM | exact: rmorph1]. Qed.
Canonical cnvar_additive := Additive cnvar_is_rmorphism.
Canonical cnvar_rmorphism := RMorphism cnvar_is_rmorphism.

Fact cnvar_is_linear : linear cnvar.
Proof. by rewrite /cnvar; exact: linearP. Qed.
Canonical cnvar_linear := AddLinear cnvar_is_linear.
Canonical cnvar_lrmorphism := [lrmorphism of cnvar].

Hypothesis (nlem : (n <= m)%N).
Lemma tnth_cnvar_tuple (i : 'I_m) (ilen : (i < n)%N) :
  tnth cnvar_tuple i = 'X_(Ordinal ilen).
Proof.
rewrite (tnth_nth 0) /= nth_cat size_take size_map size_enum_ord.
rewrite (ltnNge m n) nlem /= ilen.
rewrite nth_take ?(leq_trans ilen) //.
rewrite (nth_map (Ordinal ilen)) ?size_enum_ord //; congr ('X_ _).
by apply val_inj; rewrite /= nth_enum_ord.
Qed.

Lemma tnth_cnvar_tuple0 (i : 'I_m) : (n <= i)%N -> tnth cnvar_tuple i = 0.
Proof.
move=> nlei; rewrite (tnth_nth 0) /= nth_cat size_take size_map size_enum_ord.
by rewrite (ltnNge m n) nlem /= (ltnNge i n) nlei /= nth_nseq if_same.
Qed.

End Defs.

Lemma cnvar_id n : @cnvar n n =1 id.
Proof.
move=> p; rewrite /cnvar.
suff -> : cnvar_tuple n n = [tuple 'X_i | i < n] by rewrite comp_mpoly_id.
apply eq_from_tnth => i.
rewrite tnth_cnvar_tuple // tnth_mktuple; congr ('X_ _).
exact: val_inj.
Qed.

Lemma cnvar_compat i j k :
  (i <= j)%N -> (j <= k)%N -> (@cnvar i j) \o (@cnvar j k) =1 (@cnvar i k).
Proof.
move=> ilej jlek p /=; have ilek := leq_trans ilej jlek.
rewrite /cnvar !(comp_mpolyE p) raddf_sum /=; apply eq_bigr => m _.
rewrite comp_mpolyZ; congr (_ *: _).
rewrite rmorph_prod /=; apply eq_bigr => l _.
rewrite !rmorphX /=; congr (_ ^+ _).
case: (ltnP l i) => [llti | ilel].
- rewrite !tnth_cnvar_tuple ?(leq_trans llti ilej) // => Hlj.
  by rewrite comp_mpolyXU -tnth_nth !tnth_cnvar_tuple.
- rewrite [RHS]tnth_cnvar_tuple0 //.
  case: (ltnP l j) => [lltj|jlel].
  + by rewrite tnth_cnvar_tuple // comp_mpolyXU -tnth_nth tnth_cnvar_tuple0.
  + by rewrite tnth_cnvar_tuple0 // comp_mpoly0.
Qed.


Section InverseSys.

Definition cnvarbond (i j : nat) of (i <= j)%O := @cnvar i j.
Program Definition infpoly_sys := @InvSys _ _ _ cnvarbond 0%N _ _.
Next Obligation. exact: cnvar_id. Qed.
Next Obligation. exact: cnvar_compat. Qed.


Variables (i j : nat) (H : (i <= j)%O).
Fact cnvarbond_is_rmorphism : rmorphism (cnvarbond H).
Proof. exact: cnvar_is_rmorphism. Qed.
Canonical cnvarbond_additive := Additive cnvarbond_is_rmorphism.
Canonical cnvarbond_rmorphism := RMorphism cnvarbond_is_rmorphism.

Fact cnvarbond_is_linear : linear (cnvarbond H).
Proof. exact: cnvar_is_linear. Qed.
Canonical cnvarbond_linear := AddLinear cnvarbond_is_linear.
Canonical cnvarbond_lrmorphism := [lrmorphism of (cnvarbond H)].

End InverseSys.


End CNVars.

Section Tests.

Variable R : comRingType.

Variables (i j : nat) (H : (i <= j)%O).

(*
Check [lrmorphism of (cnvarbond H)].
Check [zmodType of {invlim infpoly_sys R}].
Check [comRingType of {invlim infpoly_sys R}].
Check [lmodType R of {invlim infpoly_sys R}].
Check [algType R of {invlim infpoly_sys R}].
 *)

Goal forall (r : R) (x y : {invlim infpoly_sys R}),
  'pi_2 (r *: (x * y)) = 'pi_2 y * 'pi_2 (r *: x).
Proof. by move=> r x y; rewrite linearZ /= mulrC scalerAr. Qed.

End Tests.

Section InfPolyTheory.
Variable R : comRingType.

Fact infpolyXP i :
  isthread (infpoly_sys R)
         (fun n => if ltnP i n is LtnNotGeq Pf then 'X_(Ordinal Pf) else 0).
Proof.
move=> m n mlen /=.
case (ltnP i m) => [iltm|mlei]; case (ltnP i n) => [iltn|nlei].
- by rewrite /cnvarbond/cnvar comp_mpolyXU -tnth_nth tnth_cnvar_tuple.
- by exfalso; have:= leq_trans iltm (leq_trans mlen nlei); rewrite ltnn.
- by rewrite /cnvarbond/cnvar comp_mpolyXU -tnth_nth tnth_cnvar_tuple0.
- by rewrite raddf0.
Qed.
Definition infpolyX i : {invlim infpoly_sys _} := InvLim (infpolyXP i).

End InfPolyTheory.
