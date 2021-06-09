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
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.



(** Clone of option nat to avoid the very confusing chain of coercions *)
(**   option -> bool -> nat                                            *)

Section NatBar.

Open Scope order_scope.


Inductive natbar : Set :=  Nat of nat | Inf.
Definition opt_natbar (v : natbar) : option nat :=
  if v is Nat n then Some n else None.
Definition natbar_opt (v : option nat) : natbar :=
  if v is Some n then Nat n else Inf.

Lemma opt_natbarK : cancel opt_natbar natbar_opt.
Proof. by case. Qed.
Lemma natbar_optK : cancel natbar_opt opt_natbar.
Proof. by case. Qed.
Definition natbar_eqMixin := CanEqMixin opt_natbarK.
Canonical natbar_eqType := Eval hnf in EqType natbar natbar_eqMixin.
Definition natbar_choiceMixin := CanChoiceMixin opt_natbarK.
Canonical natbar_choiceType := Eval hnf in ChoiceType natbar natbar_choiceMixin.
Definition natbar_countMixin := CanCountMixin opt_natbarK.
Canonical natbar_countType := Eval hnf in CountType natbar natbar_countMixin.

Implicit Type (m n o p : nat).
Implicit Type (u v w x y : natbar).

Lemma Nat_inj : injective Nat. Proof. by move=> m n []. Qed.
Lemma Nat_eqE m n : (Nat m == Nat n) = (m == n).
Proof. by apply/eqP/eqP => [/Nat_inj|<-]. Qed.

Definition addbar u v : natbar :=
  match u, v with
  | Nat m, Nat n => Nat (m + n)
  | _, _ => Inf
  end.

Lemma add0bar : left_id  (Nat 0) addbar. Proof. by case. Qed.
Lemma addbar0 : right_id (Nat 0) addbar.
Proof. by case=> //= n; rewrite addn0. Qed.

Lemma addIbar : left_zero  Inf addbar. Proof. by case. Qed.
Lemma addbarI : right_zero Inf addbar. Proof. by case. Qed.

Lemma addbarCA : left_commutative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnCA. Qed.

Lemma addbarC : commutative addbar.
Proof. by case=> [m|] [n|] //=; rewrite addnC. Qed.

Lemma addbarA : associative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnA. Qed.

Lemma addbarAC : right_commutative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnAC. Qed.

Lemma addbarACA : interchange addbar addbar.
Proof. by case=> [m|] [n|] [p|] [q|] //=; rewrite addnACA. Qed.

Lemma addbar_eq0 u v : (addbar u v == Nat 0) = (u == Nat 0) && (v == Nat 0).
Proof.
by case: u v => [m|] [n|] //=; rewrite !Nat_eqE /= ?addn_eq0 ?andbF.
Qed.

Lemma addbar_eqI u v : (addbar u v == Inf) = (u == Inf) || (v == Inf).
Proof. by case: u v => [m|] [n|]. Qed.

Canonical natbar_monoid := Monoid.Law addbarA add0bar addbar0.
Canonical natbar_comoid := Monoid.ComLaw addbarC.


(** Valuation ordering *)
Definition lebar u v :=
  match u, v with
  | _, Inf => true
  | Nat m, Nat n => m <= n
  | _, _ => false
  end.
Definition ltbar u v := (v != u) && (lebar u v).
Definition meetbar x y := if ltbar x y then x else y.
Definition joinbar x y := if ltbar x y then y else x.
Definition lebar_display : unit. Proof. exact: tt. Qed.

Program Definition natbar_OrderMixin :=
  @LeOrderMixin _ lebar ltbar meetbar joinbar _ _ _ _ _ _.
Next Obligation. by case=> [m|] [n|] //=; rewrite -eqn_leq => /eqP ->. Qed.
Next Obligation. by case=> [m|] [n|] [p|] //=; apply leq_trans. Qed.
Next Obligation. by case=> [m|] [n|] //=; exact: leq_total. Qed.

Canonical natbar_porderType :=
  Eval hnf in POrderType lebar_display natbar natbar_OrderMixin.
Canonical natbar_atticeType :=
  Eval hnf in LatticeType natbar natbar_OrderMixin.
Canonical natbar_distrLatticeType :=
  Eval hnf in DistrLatticeType natbar natbar_OrderMixin.
Canonical natbar_orderType :=
  Eval hnf in OrderType natbar natbar_OrderMixin.

Lemma le0bar v : Nat 0 <= v. Proof. by case: v. Qed.
Canonical natbar_bLatticeType :=
  Eval hnf in BLatticeType natbar (BottomMixin le0bar).

Lemma leEnatbar (n m : nat) : (Nat n <= Nat m) = (n <= m)%N.
Proof. by []. Qed.

Lemma ltEnatbar (n m : nat) : (Nat n < Nat m) = (n < m)%N.
Proof. by rewrite lt_neqAle leEnatbar Nat_eqE ltn_neqAle. Qed.

Lemma lebar_total : total lebar.
Proof. exact: le_total. Qed.

Lemma lebarI v : v <= Inf. Proof. by case v. Qed.

Canonical natbar_tbDistrLatticeType :=
  Eval hnf in TBLatticeType natbar (TopMixin lebarI).

Lemma ltbar0Sn n : 0 < Nat n.+1.       Proof. by []. Qed.
Lemma ltbarS n : Nat n < Nat n.+1.     Proof. by rewrite ltEnatbar. Qed.
Lemma lebarS n : Nat n <= Nat n.+1.    Proof. by rewrite leEnatbar. Qed.
Hint Resolve lebarS : core.
Lemma ltIbar v : Inf < v = false.      Proof. exact/le_gtF/lex1. Qed.
Lemma leInatbar n : Inf <= Nat n = false.
Proof. by []. Qed.

Lemma minbarE : {morph Nat : m n / minn m n >-> Order.meet m n}.
Proof.
move=> m n; case: (leqP m n) => [| /ltnW].
- by rewrite -leEnatbar => /meet_idPl.
- by rewrite -leEnatbar => /meet_idPr.
Qed.

Lemma maxbarE : {morph Nat : m n / maxn m n >-> Order.join m n}.
Proof.
move=> m n; case: (leqP m n) => [| /ltnW].
- by rewrite -leEnatbar => /join_idPr.
- by rewrite -leEnatbar => /join_idPl.
Qed.

End NatBar.


