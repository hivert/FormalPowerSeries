(** * Combi.directed : Directed sets *)
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
(** * Directed sets. A set \(S\) is directed if it is ordered and if forall
\(x, y\in S\) there is a \(z\in S\) such that \(x\leq z\) and \(y\leq z\).
*******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import order.

Require Import natbar.


Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition directed (T : Type) (R : T -> T -> bool) :=
  forall x y : T, { z | R x z & R y z }.

(** TODO : I'm not using anti-symmetry, i.e.: directed sets can be preorders *)
HB.mixin Record Directed (d : unit) T of Order.POrder d T := {
  directedP : directed (T := T) <=%O
}.
#[short(type="dirType")]
HB.structure Definition DirectedType d :=
  { T of Directed d T & Order.POrder d T }.

HB.factory Record Lattice_isDirected d T of Order.Lattice d T := { }.
HB.builders Context d T of Lattice_isDirected d T.

Fact lattice_directed : directed (T := T) <=%O.
Proof. by move=> x y; exists (x `|` y); [apply: leUl |apply: leUr]. Qed.
HB.instance Definition _ := Directed.Build d T lattice_directed.

HB.end.

HB.instance Definition _ := Lattice_isDirected.Build _ nat.
HB.instance Definition _ := Lattice_isDirected.Build _ natdvd.


(* This should'nt be done that way because of "broken" inheritance
However, by inserting properly dirtype in the order hierarchy, one doesn't need
to declare each instance of lattice as a dirtype as done just up there.

Section Generic.
Variables (disp : unit) (T : latticeType disp).

Fact lattice_directed : directed (T := T) <=%O.
Proof. by move=> x y; exists (x `|` y); [apply: leUl |apply: leUr]. Qed.
(* Q: non forgetful inheritance detected. *)
HB.instance Definition _ := Directed.Build disp T lattice_directed.

End Generic.

Canonical nat_dirType := DirType nat (@lattice_dirMixin _ _).
Canonical natdvd_dirType := DirType natdvd (@lattice_dirMixin _ _).

*)


(* Commented out since nee classical_sets and not needed anyway

From mathcomp Require Import boolp classical_sets.
Section UpSets.

Variables (disp : unit) (I : dirType disp).
Implicit Types (i j k : I).
Implicit Types (s t : set I).

Definition up_set (S : set I) :=
  nonempty S /\ forall i j, i <= j -> S i -> S j.

Lemma up_setI S T : up_set S -> up_set T -> up_set (S `&` T).
Proof.
move=> [[x Sx upS]] [[y Sy upT]]; split.
- have [z le_xz le_yz] := directedP x y; exists z.
  by split; [apply: upS; first exact: le_xz | apply: upT; first exact: le_yz].
by move=> i j le_ij [/(upS _ _ le_ij) Si /(upT _ _ le_ij) Sj].
Qed.
Lemma up_setU S T : up_set S -> up_set T -> up_set (S `|` T).
Proof.
move=> [[x Sx upS]] [[y Sy upT]]; split; first by exists x; left.
by move=> i j le_ij [/(upS _ _ le_ij) Si | /(upT _ _ le_ij) Sj]; [left|right].
Qed.

Variables (T : Type) (P : set T) (F : T -> set I).

Lemma up_set_bigcup :
  nonempty P ->
  (forall t : T, P t -> up_set (F t)) ->
  up_set (\bigcup_(t in P) F t).
Proof.
move=> [t Pt] H; split.
  by have [[i Fti] _] := H t Pt; exists i; exists t.
move=> {t Pt} i j le_ij [t Pt Fti]; exists t => //.
by have [_] := H t Pt; apply; first apply: le_ij.
Qed.

End UpSets.
*)
