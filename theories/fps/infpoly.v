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
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrcomplements freeg mpoly.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import natbar directed invlim dirlim_constr dirlim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Fact cnvar_is_additive : additive cnvar.
Proof. exact: rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isAdditive.Build {mpoly R[m]} {mpoly R[n]} _ cnvar_is_additive.

Fact cnvar_is_multplicative : multiplicative cnvar.
Proof.  split; [exact: rmorphM | exact: rmorph1]. Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build {mpoly R[m]} {mpoly R[n]} _ cnvar_is_multplicative.

Fact cnvar_is_linear : linear cnvar.
Proof. exact: linearP. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {mpoly R[m]} {mpoly R[n]} _ _ cnvar_is_linear.

Hypothesis (le_m_n : (m <= n)%N).
Lemma tnth_cnvar_tuple (i : 'I_m) :
  tnth cnvar_tuple i = 'X_(widen_ord le_m_n i).
Proof.
have lt_i_n := leq_trans (ltn_ord i) le_m_n.
rewrite (tnth_nth 0) /= nth_cat size_take size_map size_enum_ord.
rewrite -/(minn m n) (minn_idPl le_m_n) ltn_ord nth_take //.
rewrite (nth_map (widen_ord le_m_n i)) ?size_enum_ord //; congr ('X_ _).
by apply val_inj; rewrite /= nth_enum_ord.
Qed.

End Defs.

Lemma cnvar_id n : @cnvar n n =1 id.
Proof.
move=> p; rewrite /cnvar.
suff -> : cnvar_tuple n n = [tuple 'X_i | i < n] by rewrite comp_mpoly_id.
apply: val_inj => /=.
rewrite size_map size_enum_ord subnn /= cats0 take_oversize //.
by rewrite size_map size_enum_ord.
Qed.

Lemma cnvar_compat i j k :
  (i <= j)%N -> (j <= k)%N -> (@cnvar k j) \o (@cnvar j i) =1 (@cnvar k i).
Proof.
move=> le_i_j le_j_k p /=; have le_i_k := leq_trans le_i_j le_j_k.
rewrite /cnvar !(comp_mpolyE p) raddf_sum /=; apply eq_bigr => m _.
rewrite comp_mpolyZ; congr (_ *: _).
rewrite rmorph_prod /=; apply eq_bigr => l _.
rewrite !rmorphXn /=; congr (_ ^+ _).
rewrite !tnth_cnvar_tuple comp_mpolyXU -tnth_nth tnth_cnvar_tuple; congr ('X_ _).
exact: val_inj.
Qed.

Section DirectSys.

Definition cnvarbond (m n : nat) of (m <= n)%O := @cnvar n m.
Definition infpoly_sys :=
  @IsDirSys _ _ _ cnvarbond 0%N (fun m _ => @cnvar_id m) cnvar_compat.

Variables (m n : nat) (le_m_n : (m <= n)%O).

Fact cnvarbond_is_additive : additive (cnvarbond le_m_n).
Proof. exact: rmorphB. Qed.
HB.instance Definition _ :=
  GRing.isAdditive.Build {mpoly R[m]} {mpoly R[n]} _ cnvarbond_is_additive.

Fact cnvarbond_is_multplicative : multiplicative (cnvarbond le_m_n).
Proof.  split; [exact: rmorphM | exact: rmorph1]. Qed.
HB.instance Definition _ :=
  GRing.isMultiplicative.Build
    {mpoly R[m]} {mpoly R[n]} _ cnvarbond_is_multplicative.

Fact cnvarbond_is_linear : linear (cnvarbond le_m_n).
Proof. exact: linearP. Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {mpoly R[m]} {mpoly R[n]} _ _ cnvarbond_is_linear.

Lemma cnvarbondX (i : 'I_m) : (cnvarbond le_m_n) 'X_i = 'X_(widen_ord le_m_n i).
Proof. by rewrite /cnvarbond /cnvar comp_mpolyXU -tnth_nth tnth_cnvar_tuple. Qed.

End DirectSys.

End CNVars.


Section Tests.

Variable R : comRingType.

(*
Check {dirlim infpoly_sys R} : algType R.
Check {dirlim infpoly_sys R} : dirLimType (infpoly_sys R).
Check 'inj[{dirlim infpoly_sys R}]_1 : {mpoly R[1]} -> {dirlim infpoly_sys R}.
Check 'X_0 : {mpoly R[1]}.
*)
(* TODO : why is Coq not able to infer `{dirlim infpoly_sys R}`

Goal 'inj_1 'X_0 = 'inj_3 'X_0 :> {dirlim infpoly_sys R}.

 *)
Definition infpolyvar (i : nat) :=
  'inj[{dirlim infpoly_sys R}]_i.+1 'X_(Ordinal (ltnSn i)).

Lemma infpolyvarE i n (le_i_n : (i < n)%N) :
  infpolyvar i = 'inj[{dirlim infpoly_sys R}]_n 'X_(Ordinal le_i_n).
Proof.
rewrite /infpolyvar -(dlinjE _ (le_i_n : i.+1 <= n)%O); congr 'inj.
by rewrite cnvarbondX.
Qed.

End Tests.
