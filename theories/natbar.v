(** * Combi.natbar : Completion of the set natural numbers *)
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
(** * Completion of the set of natural numbers

- [natbar]   == the set of natural number plus the infinity
- [Nat n]    == the natural number [n] as a [natbar]
- [Inf]      == the infinity [natbar]

[natbar] is equiped with both a N-module and a top and bottom bounded total
order canonical structures.

*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import order ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Order.Syntax.
Import Order.TTheory.

(** ** Basic definition *)
(* Clone of option nat to avoid the very confusing chain of coercions *)
(*   option -> bool -> nat                                            *)
Section NatBar.

Open Scope order_scope.

Inductive natbar : Set :=  Nat of nat | Inf.
Definition opt_natbar (v : natbar) : option nat :=
  if v is Nat n then Some n else None.
Definition natbar_opt (v : option nat) : natbar :=
  if v is Some n then Nat n else Inf.

Fact opt_natbarK : cancel opt_natbar natbar_opt. Proof. by case. Qed.
Fact natbar_optK : cancel natbar_opt opt_natbar. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy natbar (can_type opt_natbarK).

Implicit Type (m n o p : nat).
Implicit Type (u v w x y : natbar).

Lemma Nat_inj : injective Nat. Proof. by move=> m n []. Qed.
Lemma Nat_eqE m n : (Nat m == Nat n) = (m == n).
Proof. by apply/eqP/eqP => [/Nat_inj|<-]. Qed.

(** ** Algebraic operations *)
Definition addbar u v : natbar := match u, v with
  | Nat m, Nat n => Nat (m + n)
  | _, _ => Inf
  end.
Definition mulbar u v : natbar := match u, v with
  | Nat m, Nat n => Nat (m * n)
  | _, _ => Inf
  end.

Fact add0bar : left_id  (Nat 0) addbar. Proof. by case. Qed.
Fact addbar0 : right_id (Nat 0) addbar.
Proof. by case=> //= [n]; rewrite  /= addn0. Qed.
Fact addIbar : left_zero  Inf addbar. Proof. by case. Qed.
Fact addbarI : right_zero Inf addbar. Proof. by case. Qed.
Fact addbarC : commutative addbar.
Proof. by case=> [m|] [n|] //=; rewrite addnC. Qed.
Fact addbarA : associative addbar.
Proof. by case=> [m|] [n|] [p|] //=; rewrite addnA. Qed.
HB.instance Definition _ :=
  GRing.isNmodule.Build natbar addbarA addbarC add0bar.
Fact Nat_semi_additive : semi_additive Nat.
Proof. by []. Qed.
HB.instance Definition _ :=
  GRing.isSemiAdditive.Build _ _ Nat Nat_semi_additive.

Lemma addbar_eq0 u v : (addbar u v == Nat 0) = (u == Nat 0) && (v == Nat 0).
Proof.
by case: u v => [m|] [n|] //=; rewrite !Nat_eqE /= ?addn_eq0 ?andbF.
Qed.

Lemma addbar_eqI u v : (addbar u v == Inf) = (u == Inf) || (v == Inf).
Proof. by case: u v => [m|] [n|]. Qed.

(** ** Ordering *)
Definition lebar u v :=
  match u, v with
  | _, Inf => true
  | Nat m, Nat n => m <= n
  | _, _ => false
  end.
Definition lebar_display : unit. Proof. exact: tt. Qed.

Fact lebar_refl : reflexive lebar.
Proof. by case=> [m|] /=. Qed.
Fact lebar_anti : antisymmetric lebar.
Proof. by case=> [m|] [n|] //=; rewrite -eqn_leq => /eqP ->. Qed.
Fact lebar_trans : transitive lebar.
Proof. by case=> [m|] [n|] [p|] //=; exact: leq_trans. Qed.
Fact lebar_total : total lebar.
Proof. by case=> [m|] [n|] //=; exact: leq_total. Qed.
HB.instance Definition _ :=
    Order.Le_isPOrder.Build lebar_display natbar lebar_refl lebar_anti lebar_trans.
HB.instance Definition _ :=
    Order.POrder_isTotal.Build lebar_display natbar lebar_total.

Fact le0bar v : Nat 0 <= v. Proof. by case: v. Qed.
HB.instance Definition _ :=
  Order.hasBottom.Build lebar_display natbar le0bar.
Fact lebarI v : v <= Inf. Proof. by case v. Qed.
HB.instance Definition _ :=
  Order.hasTop.Build lebar_display natbar lebarI.

Lemma leEnatbar (n m : nat) : (Nat n <= Nat m) = (n <= m)%N.
Proof. by []. Qed.
Lemma ltEnatbar (n m : nat) : (Nat n < Nat m) = (n < m)%N.
Proof. by rewrite lt_neqAle leEnatbar Nat_eqE ltn_neqAle. Qed.

Lemma omorphNat_subproof : Order.order_morphism Nat.
Proof. by move=> x y; rewrite leEnatbar leEnat. Qed.
HB.instance Definition _ :=
  Order.isOrderMorphism.Build _ _ _ _ Nat omorphNat_subproof.

Lemma botEnatbar : \bot = Nat 0 :> natbar. Proof. by []. Qed.
Lemma topEnatbar : \top = Inf :> natbar.   Proof. by []. Qed.

(* Used to Work without Nat before 0 *)
Lemma ltbar0Sn n : Nat 0 < Nat n.+1.   Proof. by []. Qed.
Lemma ltbarS n : Nat n < Nat n.+1.     Proof. by rewrite ltEnatbar. Qed.
Lemma lebarS n : Nat n <= Nat n.+1.    Proof. by rewrite leEnatbar. Qed.
Hint Resolve lebarS : core.
Lemma ltIbar v : Inf < v = false.      Proof. exact/le_gtF/lex1. Qed.
Lemma leInatbar n : Inf <= Nat n = false.
Proof. by []. Qed.

(* Q: Anything particular to have a morphism here ? *)
Lemma minEnatbar : {morph Nat : m n / minn m n >-> Order.meet m n}.
Proof.
move=> m n; case: (leqP m n) => [| /ltnW].
- by rewrite -leEnatbar => /meet_idPl.
- by rewrite -leEnatbar => /meet_idPr.
Qed.
Lemma maxEnatbar : {morph Nat : m n / maxn m n >-> Order.join m n}.
Proof.
move=> m n; case: (leqP m n) => [| /ltnW].
- by rewrite -leEnatbar => /join_idPr.
- by rewrite -leEnatbar => /join_idPl.
Qed.

Lemma meetmorphNat_subproof : Order.meet_morphism Nat.
Proof. by move=> x y; rewrite -minEnatbar -minEnat. Qed.
Lemma joinmorphNat_subproof : Order.join_morphism Nat.
Proof. by move=> x y; rewrite -maxEnatbar -maxEnat. Qed.

HB.instance Definition _ :=
  Order.isLatticeMorphism.Build _ _ _ _ Nat
    meetmorphNat_subproof joinmorphNat_subproof.

Lemma botmorphNat_subproof : Nat \bot = \bot.
Proof. by []. Qed.

HB.instance Definition _ :=
  Order.isBLatticeMorphism.Build _ _ _ _ Nat botmorphNat_subproof.

End NatBar.
