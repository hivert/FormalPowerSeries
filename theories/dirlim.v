(******************************************************************************)
(*       Copyright (C) 2021 Florent Hivert <florent.hivert@lri.fr>            *)
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

Require Import natbar directed.


Import Order.Syntax.
Import Order.Theory.
Open Scope order_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'dirlim' S }"
         (at level 0, format "{ 'dirlim'  S }").
Reserved Notation "''inj_' i" (at level 8, i at level 2, format "''inj_' i").



(***************************************************************************)
(** Direct systems and direct limits                                       *)
(*                                                                         *)
(***************************************************************************)
Section DirectSystem.

Variables (disp : unit) (I : dirType disp).

(** Objects and bonding morphisms of the direct system at left outside     *)
(** the record below to allows the addition of more algebraic structure    *)
(** For example : ringType / rmorphism.                                    *)
Variable Ob : I -> Type.
Variable bonding : (forall i j, i <= j -> Ob i -> Ob j).
Record dirsys : Type := DirSys {
      dirsys_inh : I;
      dirsys_id  : forall i (Hii : i <= i), (bonding Hii) =1 id;
      dirsys_comp : forall i j k  (Hij : i <= j) (Hjk : j <= k),
          (bonding Hjk) \o (bonding Hij) =1 (bonding (le_trans Hij Hjk));
  }.

(** Make sure the following definitions depend on the system and not only  *)
(** on the morphisms. This is needed to triger the unification in the      *)
(** notation {invlim S} and to get the inhabitant of I.                    *)
Definition dirsys_obj of dirsys := Ob.
Definition dirsys_mor of dirsys := bonding.

Lemma bondingE i j (Hij1 Hij2 : i <= j) : bonding Hij1 =1 bonding Hij2.
Proof. by rewrite (Prop_irrelevance Hij1 Hij2). Qed.

Lemma bonding_transE (Sys : dirsys) i j k (Hij : i <= j) (Hjk : j <= k) x :
  (bonding Hjk) (bonding Hij x) = bonding (le_trans Hij Hjk) x.
Proof. by move/dirsys_comp : Sys; apply. Qed.

(* Is cocone *)
Definition iscompat of dirsys := fun T (mors : forall i, Ob i -> T) =>
  forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

(* Is section ? *)
Definition isthread of dirsys :=
  fun (thread : set I * forall i, Ob i) =>
    let: (supp, thr) := thread in
    up_set supp /\
    forall i j, supp i -> forall (Hij : i <= j), bonding Hij (thr i) = thr j.

End DirectSystem.



(***************************************************************************)
(** Interface for direct limits                                            *)
(*                                                                         *)
(***************************************************************************)
Module DirLim.


Section ClassDefs.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Record mixin_of (TLim : Type) := Mixin {
  dirlim_inj : forall i, Ob i -> TLim;
  dirlim_ind : forall (T : Type) (f : forall i, Ob i -> T),
      (iscompat Sys f) -> TLim -> T;
  _ : iscompat Sys dirlim_inj;
  _ : forall (T : Type) (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f),
      forall i, dirlim_ind Hcomp \o @dirlim_inj i =1 f i;
  _ : forall (T : Type) (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f),
      forall (ind : TLim -> T),
        (forall i, ind \o @dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind Hcomp
  }.

Record class_of T := Class {base : Choice.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Choice.class_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.

End ClassDefs.


Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation dirLimType := type.
Notation DirLimMixin := Mixin.

Section InternalTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.
Variable dlT : dirLimType Sys.

Definition inj_phant of phant dlT := dirlim_inj (mixin (class dlT)).
Local Notation "\inj" := (@inj_phant (Phant dlT)).
Local Notation "\inj_ i" := (@inj_phant (Phant dlT) i) (at level 5).
Definition ind_phant of phant dlT := dirlim_ind (mixin (class dlT)).
Local Notation "\ind" := (ind_phant (Phant dlT)).

Lemma inj_compat : iscompat Sys \inj.
Proof. by rewrite /inj_phant; case: dlT => /= [TLim [eqM []]]. Qed.

Lemma ind_commute T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) :
  forall i, \ind Hcomp \o \inj_ i =1 f i.
Proof. by rewrite /inj_phant /ind_phant; case: dlT => /= [TLim [eqM []]]. Qed.

Lemma injindE  T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) i x :
  (\ind Hcomp) (\inj_ i x) = f i x.
Proof. exact: ind_commute. Qed.

Lemma ind_uniq T (f : forall i, Ob i -> T) (Hcomp : iscompat Sys f) :
  forall (ind : dlT -> T),
    (forall i, ind \o \inj_ i =1 f i) -> ind =1 \ind Hcomp.
Proof.
rewrite /inj_phant /ind_phant.
case: dlT => /= [TLim [eqM /= [pi ind comp comm uniq]]] indT commT t /=.
by apply uniq; apply commT.
Qed.

End InternalTheory.

End Exports.
End DirLim.
Export DirLim.Exports.

Notation DirLimType T m := (@DirLim.pack _ _ _ _ _ T m _ _ id).
Notation "[ 'dirLimType' 'of' T 'for' cT ]" :=
  (@DirLim.clone _ _ _ _ _ T cT _ idfun)
  (at level 0, format "[ 'dirLimType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'dirLimType' 'of' T ]" :=
  (@DirLim.clone _ _ _ _ _ T _ _ id)
  (at level 0, format "[ 'dirLimType'  'of'  T ]") : form_scope.

Notation "''inj[' TLim ']_' i" := (@inj_phant _ _ _ _ _ TLim (Phant _) i)
                              (at level 8, i at level 2, only parsing).
Notation "''inj[' TLim ']'" := ('inj[TLim]_ _) (at level 8).
Notation "''inj_' i" := ('inj[ _ ]_ i).
Notation "''inj'" := ('inj[ _ ]_ _).
Notation "\ind" := (ind_phant (Phant _)).




Section DirLimitCongr.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> Type.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Implicit Types (i j k : I).


Definition dlcongr i j (x : Ob i) (y : Ob j) :=
  exists k (le_ik : i <= k) (le_jk : j <= k), bonding le_ik x = bonding le_jk y.

Lemma dlcongr_bonding i j (le_ij : i <= j) (x : Ob i) :
  dlcongr x (bonding le_ij x).
Proof.
exists j; exists le_ij; exists (lexx j).
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dlcongr_refl i (x : Ob i) : dlcongr x x.
Proof. by exists i; exists (lexx i); exists (lexx i). Qed.
Lemma dlcongr_sym_impl i j (x : Ob i) (y : Ob j) : dlcongr x y -> dlcongr y x.
Proof.
move=> [k [le_ik] [le_jk] Hbond].
by exists k; exists le_jk; exists le_ik; rewrite Hbond.
Qed.
Lemma dlcongr_sym i j (x : Ob i) (y : Ob j) : dlcongr x y = dlcongr y x.
Proof. by rewrite propeqE; split; apply: dlcongr_sym_impl. Qed.
Lemma dlcongr_trans i j k (x : Ob i) (y : Ob j) (z : Ob k) :
  dlcongr x y -> dlcongr y z -> dlcongr x z.
Proof.
move=> [l [le_il] [le_jl] Hxy].
move=> [m [le_jm] [le_km] Hyz].
have [n le_ln le_mn] := directedP l m.
exists n; exists (le_trans le_il le_ln); exists (le_trans le_km le_mn).
rewrite -!bonding_transE // {}Hxy -{}Hyz !bonding_transE //.
exact: bondingE.
Qed.

Lemma dlcongr_compat i (x : Ob i) :
  iscompat Sys (fun j (y : Ob j) => `[< dlcongr x y >]).
Proof.
move=> j k le_jk y /=.
case: (boolP `[< dlcongr x y >]) => [Hthr | Hnthr].
- move: Hthr => /asboolP [l [le_il] [le_jl] Hbond]; apply/asboolP.
  have [m le_km le_lm] := directedP k l.
  exists m; exists (le_trans le_il le_lm); exists (le_km).
  rewrite -(dirsys_comp Sys le_il le_lm) /= Hbond.
  by rewrite !bonding_transE //; apply: bondingE.
- apply/negP => /= /asboolP [l [le_il] [le_kl]].
  rewrite bonding_transE // => Hbond.
  move: Hnthr => /asboolP; apply.
  by exists l; exists le_il; exists (le_trans le_jk le_kl).
Qed.

Variable TLim : dirLimType Sys.

Lemma dirlimP (t : TLim) : exists k (y : Ob k), 'inj y = t.
Proof.
rewrite not_existsP => H.
pose f i := pred0 (T := Ob i).
have Hcomp : iscompat Sys f by [].
have /(ind_uniq Hcomp)/(_ t) :
  forall i, (pred0 (T := TLim)) \o 'inj =1 f i by [].
suff /(ind_uniq Hcomp)/(_ t) <- : forall i, (pred1 t) \o 'inj =1 f i.
  by rewrite /= eqxx.
rewrite /f => i x /=; apply/negP => /eqP eq_inj.
by apply/(H i); exists x.
Qed.

Lemma dirlim_pairP (t : TLim) : { p : {i & Ob i} | 'inj (projT2 p) = t }.
Proof.
by apply cid; case: (dirlimP t) => i [x eqinj]; exists (existT _ i x).
Qed.

End DirLimitCongr.


Section DirLimitChoiceType.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Implicit Types (i j k : I) (p q : {i & Ob i}).
Local Notation dlc := (dlcongr bonding).

Lemma dlcanon_ex p : exists q, (fun q => `[< dlc (projT2 p) (projT2 q)>]) q.
Proof. by exists p; apply/asboolP/dlcongr_refl. Qed.
Definition dlcanon p : {i & Ob i} := xchoose (dlcanon_ex p).

Lemma dlcanonP p : dlc (projT2 p) (projT2 (dlcanon p)).
Proof.
apply/asboolP.
exact: (@xchooseP _ (fun q => `[< dlc (projT2 p) (projT2 q)>])).
Qed.
Lemma dlcanonE p q : dlc (projT2 p) (projT2 q) <-> dlcanon p = dlcanon q.
Proof.
split => [|Heq].
- rewrite /dlcanon => Hcongr; apply: eq_xchoose => /= x.
  apply: asbool_equiv_eq; split; apply: dlcongr_trans => //.
  exact: dlcongr_sym_impl.
- rewrite dlcongr_sym; have /(dlcongr_trans Sys) := dlcanonP q; apply.
  rewrite dlcongr_sym -Heq.
  exact: dlcanonP.
Qed.

Lemma dlcanon_id p : invariant dlcanon dlcanon p.
Proof.
rewrite /invariant; apply/eqP/dlcanonE.
by rewrite dlcongr_sym; apply: dlcanonP.
Qed.

Variable TLim : dirLimType Sys.
Implicit Types (t a b c : TLim).

Lemma dirlimEI (i : I) (x : Ob i) (y : Ob i) :
  'inj[TLim] x = 'inj[TLim] y ->
  exists (k : I) (le_ik : i <= k), bonding le_ik x = bonding le_ik y.
Proof.
move => Heq; apply contrapT; rewrite -forallNP => Hbond.
have Hcomp := dlcongr_compat Sys y.
have:= injindE TLim Hcomp y; rewrite -Heq injindE.
have /asboolP -> := dlcongr_refl bonding y.
move=> /asboolP [j [le_ij] [le_ij2]] Habs.
apply: (Hbond j); exists (le_ij); rewrite Habs.
exact: bondingE.
Qed.

Lemma dirlimE (i j : I) (x : Ob i) (y : Ob j) :
  ('inj[TLim] x = 'inj[TLim] y) <-> (dlcongr bonding x y).
Proof.
split => [H | [k [le_ik] [le_jk] Hbond]].
- have [l le_il le_jl] := directedP i j.
  have /dirlimEI [k [le_lk]] :
      'inj[TLim] (bonding le_il x) = 'inj[TLim] (bonding le_jl y).
    have /= -> := (inj_compat TLim le_il x).
    by rewrite H -(inj_compat TLim le_jl y).
  rewrite !bonding_transE // => Hk.
  by exists k; exists (le_trans le_il le_lk); exists (le_trans le_jl le_lk).
- have /= <- := (inj_compat TLim le_ik x).
  by rewrite Hbond -(inj_compat TLim le_jk y).
Qed.

Lemma dlrepc_ex t :
  exists q, (fun q => `[< 'inj (projT2 q) = t >]) q.
Proof. by case: (dirlim_pairP t) => p Hp; exists p; apply/asboolP. Qed.
Definition dlrepr t : {i & Ob i} := xchoose (dlrepc_ex t).

Lemma dlreprP t : 'inj (projT2 (dlrepr t)) = t.
Proof.
apply/asboolP.
exact: (@xchooseP _ (fun q : {i & Ob i} => `[< 'inj (projT2 q) = t >])).
Qed.

Lemma dlrepr_dlcanonE t p : 'inj (projT2 p) = t -> dlcanon p = dlrepr t.
Proof.
move=> <- {t}; apply: eq_xchoose => [[i x]] /=.
by apply: asbool_equiv_eq; rewrite dirlimE dlcongr_sym.
Qed.

Lemma get_repr2 a b :
  exists i (x y : Ob i), 'inj x = a /\ 'inj y = b.
Proof.
case: (dlrepr a) (dlreprP a) => /= ia ra <-{a}.
case: (dlrepr b) (dlreprP b) => /= ib rb <-{b}.
case: (directedP ia ib) => n le_ian le_ibn.
exists n; exists (bonding le_ian ra); exists (bonding le_ibn rb).
by split; have /= -> := (inj_compat TLim) _ _ _ _.
Qed.
Lemma get_repr3 a b c :
  exists i (x y z : Ob i), [/\ 'inj x = a, 'inj y = b & 'inj z = c].
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
case: (dlrepr c) (dlreprP c) => /= j z <-{c}.
case: (directedP i j) => n le_in le_jn.
exists n; exists (bonding le_in x); exists (bonding le_in y);
  exists (bonding le_jn z).
by split; have /= -> := (inj_compat TLim) _ _ _ _.
Qed.

End DirLimitChoiceType.

(****************************************************************************)
(** Direct limits in various algebraic categories                           *)
(**                                                                         *)
(** We don't deal with multiplicative groups as they are all assumed finite *)
(** in mathcomp.                                                            *)
(****************************************************************************)

Open Scope ring_scope.
Import GRing.Theory.

Module DirLimitZMod.
Section DirLimitZMod.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Local Notation dlc := (dlcongr _).

Variable TLim : dirLimType Sys.
Implicit Types a b c : TLim.


Definition dlzero  : TLim := 'inj_(dirsys_inh Sys) 0.
Definition dlopp a : TLim := 'inj (-projT2 (dlrepr a)).
Definition dladd a b : TLim :=
  let: existT i x := dlrepr a in
  let: existT j y := dlrepr b in
  let: exist2 k le_ik le_jk := directedP i j in
  'inj (bonding le_ik x + bonding le_jk y).

Lemma dlzeroE i : dlzero = 'inj_i 0.
Proof.
rewrite /dlzero dirlimE.
case: (directedP (dirsys_inh Sys) i) => j le_j le_ij.
exists j; exists le_j; exists le_ij.
by rewrite !raddf0.
Qed.
Lemma dloppE i (x : Ob i) : dlopp ('inj x) = 'inj (-x).
Proof.
rewrite /dlzero dirlimE.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra.
rewrite dirlimE => [[j] [le_iaj] [le_ij]] Hbond.
exists j; exists le_iaj; exists le_ij.
by rewrite !raddfN Hbond.
Qed.
Lemma dladdE i (x : Ob i) (y : Ob i) : dladd ('inj x) ('inj y) = 'inj (x + y).
Proof.
rewrite /dladd.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra Hra.
case: (dlrepr ('inj[TLim] y)) (dlreprP ('inj[TLim] y)) => /= ib rb Hrb.
case: directedP => m le_iam le_ibm.
move: Hra; rewrite dirlimE => [[ja] [le_iaja] [le_ija] Hbonda].
move: Hrb; rewrite dirlimE => [[jb] [le_ibjb] [le_ijb] Hbondb].
case: (directedP ja jb) => n le_jan le_jbn.
case: (directedP m n) => bnd le_mbnd le_nbnd.
rewrite dirlimE; exists bnd; exists le_mbnd.
exists (le_trans le_ija (le_trans le_jan le_nbnd)).
rewrite !raddfD /= -!(bonding_transE Sys) -{}Hbonda.
have -> : bonding le_jan (bonding le_ija y) = bonding le_jbn (bonding le_ijb y).
  by rewrite !(bonding_transE Sys); apply (bondingE bonding).
rewrite -{}Hbondb.
by congr (_ + _); rewrite !(bonding_transE Sys); apply (bondingE bonding).
Qed.

Program Definition dirlim_zmodMixin of phant TLim :=
  @ZmodMixin TLim dlzero dlopp dladd _ _ _ _.
Next Obligation.
move=> a b c.
case: (get_repr3 a b c) => i [x] [y] [z] [<-{a} <-{b} <-{c}].
by rewrite !dladdE addrA.
Qed.
Next Obligation.
move=> a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite !dladdE addrC.
Qed.
Next Obligation.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia ra <-{a}.
by rewrite (dlzeroE ia) dladdE add0r.
Qed.
Next Obligation.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia ra <-{a}.
by rewrite dloppE dladdE addNr -dlzeroE.
Qed.

(* Not global canonical but accessible by [zmodMixin of ... by <-] *)
(* A mettre dans un module pour avoir le canonical local *)

Local Canonical dirlim_zmodType :=
  Eval hnf in ZmodType TLim (dirlim_zmodMixin (Phant TLim)).

Lemma dl0E : exists i, 'inj[TLim]_i 0 = 0.
Proof. by rewrite {2}/GRing.zero; exists (dirsys_inh Sys). Qed.

Fact dlinj_is_additive i : additive 'inj_i.
Proof.
by move=> x y; rewrite {2}/GRing.opp /= dloppE {2}/GRing.add /= dladdE.
Qed.
Canonical dlinj_additive i : {additive Ob i -> TLim} :=
  Additive (@dlinj_is_additive i).

(** The universal induced map is a Z-module morphism *)
Section UniversalProperty.

Variable (T : zmodType) (f : forall i, {additive (Ob i) -> T}).
Hypothesis Hcomp : iscompat Sys f.

Fact dlind_is_additive : additive (\ind Hcomp).
Proof.
move=> a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -raddfB /= !injindE -raddfB.
Qed.
Canonical dlind_additive : {additive TLim -> T} :=
  Additive dlind_is_additive.

End UniversalProperty.

End DirLimitZMod.
End DirLimitZMod.

Notation "[ 'zmodMixin' 'of' U 'by' <- ]" :=
  (DirLimitZMod.dirlim_zmodMixin (Phant U))
  (at level 0, format "[ 'zmodMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_additive := DirLimitZMod.dlinj_additive.
Canonical dlind_additive := DirLimitZMod.dlind_additive.
Definition dl0E := DirLimitZMod.dl0E.


Module DirLimitRing.
Section DirLimitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type a b c : TLim.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].

Definition dlone  : TLim := 'inj_(dirsys_inh Sys) 1.
Lemma dloneE i : dlone = 'inj_i 1.
Proof.
rewrite /dlone dirlimE.
case: (directedP (dirsys_inh Sys) i) => j le_j le_ij.
exists j; exists le_j; exists le_ij.
by rewrite !rmorph1.
Qed.

Definition dlmul a b : TLim :=
  let: existT i x := dlrepr a in
  let: existT j y := dlrepr b in
  let: exist2 k le_ik le_jk := directedP i j in
  'inj (bonding le_ik x * bonding le_jk y).

Lemma dlmulE i (x : Ob i) (y : Ob i) : dlmul ('inj x) ('inj y) = 'inj (x * y).
Proof.
rewrite /dlmul.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra Hra.
case: (dlrepr ('inj[TLim] y)) (dlreprP ('inj[TLim] y)) => /= ib rb Hrb.
case: directedP => m le_iam le_ibm.
move: Hra; rewrite dirlimE => [[ja] [le_iaja] [le_ija] Hbonda].
move: Hrb; rewrite dirlimE => [[jb] [le_ibjb] [le_ijb] Hbondb].
case: (directedP ja jb) => n le_jan le_jbn.
case: (directedP m n) => bnd le_mbnd le_nbnd.
rewrite dirlimE; exists bnd; exists le_mbnd.
exists (le_trans le_ija (le_trans le_jan le_nbnd)).
rewrite !rmorphM /= -!(bonding_transE Sys) -{}Hbonda.
have -> : bonding le_jan (bonding le_ija y) = bonding le_jbn (bonding le_ijb y).
  by rewrite !(bonding_transE Sys); apply (bondingE bonding).
rewrite -{}Hbondb.
by congr (_ * _); rewrite !(bonding_transE Sys); apply (bondingE bonding).
Qed.

Program Definition dirlim_ringMixin of phant TLim :=
  @RingMixin _ dlone dlmul _ _ _ _ _ _.
Next Obligation.
move=> a b c.
case: (get_repr3 a b c) => i [x] [y] [z] [<-{a} <-{b} <-{c}].
by rewrite !dlmulE mulrA.
Qed.
Next Obligation.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia ra <-{a}.
by rewrite (dloneE ia) dlmulE mul1r.
Qed.
Next Obligation.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia ra <-{a}.
by rewrite (dloneE ia) dlmulE mulr1.
Qed.
Next Obligation.
move=> a b c.
case: (get_repr3 a b c) => i [x] [y] [z] [<-{a} <-{b} <-{c}].
by rewrite !dlmulE -!raddfD /= -mulrDl dlmulE.
Qed.
Next Obligation.
move=> a b c.
case: (get_repr3 a b c) => i [x] [y] [z] [<-{a} <-{b} <-{c}].
by rewrite !dlmulE -!raddfD /= -mulrDr dlmulE.
Qed.
Next Obligation.
apply/negP => /eqP.
rewrite /GRing.zero /= /DirLimitZMod.dlzero /dlone.
rewrite dirlimE => [[i] [le1] [le2]].
by rewrite rmorph0 rmorph1 => /eqP; rewrite oner_eq0.
Qed.
Local Canonical dirlim_ringType :=
  Eval hnf in RingType TLim (dirlim_ringMixin (Phant TLim)).

Lemma dl1E : exists i, 'inj[TLim]_i 1 = 1.
Proof. by rewrite {2}/GRing.one; exists (dirsys_inh Sys). Qed.


Fact dlinj_is_multiplicative i : multiplicative 'inj_i.
Proof.
split => [a b|].
- by rewrite {2}/GRing.mul /= dlmulE.
- by rewrite {2}/GRing.one /= (dloneE i).
Qed.
Canonical dlinj_rmorphism i : {rmorphism Ob i -> TLim} :=
  AddRMorphism (dlinj_is_multiplicative i).

Section UniversalProperty.

Variable (T : ringType) (f : forall i, {rmorphism (Ob i) -> T}).
Hypothesis Hcomp : iscompat Sys f.

Fact dlind_is_multiplicative : multiplicative (\ind Hcomp).
Proof.
split.
- move=> a b.
  case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
  by rewrite -rmorphM /= !injindE -rmorphM.
- by rewrite {1}/GRing.one /= injindE rmorph1.
Qed.
Canonical dlind_rmorphism : {rmorphism TLim -> T} :=
  AddRMorphism dlind_is_multiplicative.

End UniversalProperty.

End DirLimitRing.
End DirLimitRing.

Notation "[ 'ringMixin' 'of' U 'by' <- ]" :=
  (DirLimitRing.dirlim_ringMixin (Phant U))
  (at level 0, format "[ 'ringMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_multiplicative := DirLimitRing.dlinj_rmorphism.
Canonical dlind_multiplicative := DirLimitRing.dlind_rmorphism.
Definition dl1E := DirLimitRing.dl1E.


Module DirLimitComRing.
Section DirLimitComRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type a b : TLim.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].

Fact ilmulC a b : a * b = b * a.
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -!rmorphM /= mulrC.
Qed.
Definition dirlim_comRingMixin of phant TLim := ilmulC.

End DirLimitComRing.
End DirLimitComRing.

Notation "[ 'comRingMixin' 'of' U 'by' <- ]" :=
  (DirLimitComRing.dirlim_comRingMixin (Phant U))
  (at level 0, format "[ 'comRingMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitUnitRing.
Section DirLimitUnitRing.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type x y : TLim.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].

Definition dlunit x :=
  `[exists p : {i & Ob i},
       ('inj[TLim] (projT2 p) == x) && (projT2 p \is a GRing.unit)].
Definition dlinv x : TLim :=
  if (boolP (dlunit x)) is AltTrue pf then
    let p := xchooseb pf in 'inj ((projT2 p)^-1) else x.

Program Definition dirlim_unitRingMixin of (phant TLim) :=
  Eval hnf in @UnitRingMixin _ dlunit dlinv _ _ _ _.
Next Obligation.
move=> a.
rewrite /dlinv unfold_in -/(dlunit a).
case (boolP (dlunit a)) => //; rewrite /dlunit => Hunit _.
have /andP [/eqP Heq Hun] := xchoosebP Hunit.
by rewrite -[X in _* X]Heq -rmorphM /= mulVr // rmorph1.
Qed.
Next Obligation.
move=> a.
rewrite /dlinv unfold_in -/(dlunit a).
case (boolP (dlunit a)) => //; rewrite /dlunit => Hunit _.
have /andP [/eqP Heq Hun] := xchoosebP Hunit.
by rewrite -[X in X * _]Heq -rmorphM /= mulrV // rmorph1.
Qed.
Next Obligation.
case: dl1E => [i1 Hi1].
case: (get_repr2 x y) => i [u] [v] [Hx Hy]; subst x y.
move: H0 H1; rewrite -!rmorphM /= -{}Hi1.
rewrite dirlimE => [[il] [le_i_il] [le_il] Hl].
rewrite dirlimE => [[ir] [le_i_ir] [le_ir] Hr].
move: Hl Hr; rewrite !rmorphM !rmorph1 {le_il le_ir i1}.
case: (directedP il ir) => m le_ilm le_irm.
move/(congr1 (bonding le_ilm)); rewrite !rmorphM rmorph1 => Hl.
move/(congr1 (bonding le_irm)); rewrite !rmorphM rmorph1 => Hr.
move: Hl Hr; rewrite !(bonding_transE Sys).
have -> : bonding (le_trans le_i_il le_ilm) u = bonding (le_trans le_i_ir le_irm) u.
  exact: (bondingE bonding).
have -> : bonding (le_trans le_i_il le_ilm) v = bonding (le_trans le_i_ir le_irm) v.
  exact: (bondingE bonding).
set bu := bonding _ u; set bv := bonding _ v => Hvu Huv.
apply/existsbP; exists (existT _ m bu) => /=; apply/andP; split.
  by rewrite /bu; have /= -> := inj_compat TLim _ u.
by apply/unitrP; exists bv.
Qed.
Next Obligation.
move=> a; rewrite /dlinv; case (boolP (dlunit a)) => // H1 H2; exfalso.
by move: H2; rewrite inE /=; have -> : a \in dlunit by [].
Qed.
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim (dirlim_unitRingMixin (Phant TLim)).

Lemma dlunitP a :
  reflect (exists i (x : Ob i), 'inj[TLim] x = a /\ x \is a GRing.unit)
          (a \is a GRing.unit).
Proof.
rewrite {2}/GRing.unit /= unfold_in /dlunit; apply (iffP (existsbP _)).
- by move=> [[i x]/= /andP[/eqP Heq Hunit]]; exists i; exists x.
- by move=> [i] [x] [<- Hunit]; exists (existT _ i x); rewrite eq_refl.
Qed.

End DirLimitUnitRing.
End DirLimitUnitRing.

Notation "[ 'unitRingMixin' 'of' U 'by' <- ]" :=
  (DirLimitUnitRing.dirlim_unitRingMixin (Phant U))
  (at level 0, format "[ 'unitRingMixin'  'of'  U  'by'  <- ]") : form_scope.

Definition dlunitP := DirLimitUnitRing.dlunitP.


Module DirLimitIDomain.
Section DirLimitIDomain.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (x y : TLim).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical TLim_comRingType :=
  Eval hnf in ComRingType TLim [comRingMixin of TLim by <-].
Local Canonical TLim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].

Fact dlmul_eq0 x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> Heq; apply/orP.
case: dl0E => [i0 Hi0].
case: (get_repr2 x y) => i [u] [v] [Hx Hy]; subst x y.
move: Heq; rewrite -!rmorphM /= -{}Hi0.
rewrite dirlimE => [[l] [le_il] [le_i0l]].
rewrite !rmorphM !rmorph0 {le_i0l i0} => /eqP.
by rewrite mulf_eq0 => /orP [] /eqP /(congr1 'inj[TLim]) H; [left|right];
   move: H; have /= -> := inj_compat TLim _ _ => ->; rewrite rmorph0.
Qed.
Definition dirlim_idomainMixin of phant TLim := dlmul_eq0.

End DirLimitIDomain.
End DirLimitIDomain.

Notation "[ 'idomainMixin' 'of' U 'by' <- ]" :=
  (DirLimitIDomain.dirlim_idomainMixin (Phant U))
  (at level 0, format "[ 'idomainMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitLinear.
Section DirLimitLinear.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b c : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].

Definition dlscale r a : TLim := 'inj (r *: projT2 (dlrepr a)).

Lemma dlscaleE r i (x : Ob i) : dlscale r ('inj x) = 'inj (r *: x).
Proof.
rewrite dirlimE.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra.
rewrite dirlimE => [[j] [le_iaj] [le_ij]] Hbond.
exists j; exists le_iaj; exists le_ij.
by rewrite !linearZ Hbond.
Qed.

Program Definition dirlim_lmodMixin of phant TLim :=
  @LmodMixin R [zmodType of TLim] dlscale _ _ _ _.
Next Obligation.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite [dlscale b _]dlscaleE !dlscaleE scalerA.
Qed.
Next Obligation.
move=> v.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite dlscaleE scale1r.
Qed.
Next Obligation.
move=> r a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite !dlscaleE -!raddfD /= dlscaleE.
Qed.
Next Obligation.
move=> r s.
case: (dlrepr v) (dlreprP v) => /= iv rv <-{v}.
by rewrite !dlscaleE -raddfD /= -scalerDl.
Qed.
Local Canonical dirlim_lmodType :=
  Eval hnf in LmodType R TLim (dirlim_lmodMixin (Phant TLim)).

Fact dlinj_is_linear i : linear 'inj_i.
Proof.
move=> r a b.
by rewrite [in RHS]/GRing.scale /= dlscaleE -raddfD.
Qed.
Canonical dlinj_linear i : {linear Ob i -> TLim } :=
  AddLinear (@dlinj_is_linear i).


Section UniversalProperty.

Variable (T : lmodType R) (f : forall i, {linear (Ob i) -> T}).
Hypothesis Hcomp : iscompat Sys f.

Fact dlind_is_linear : linear (\ind Hcomp).
Proof.
move=> /= r a b.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearP !injindE -linearP.
Qed.
Canonical dlind_linear : {linear TLim -> T} := AddLinear dlind_is_linear.

End UniversalProperty.

End DirLimitLinear.
End DirLimitLinear.

Notation "[ 'lmodMixin' 'of' U 'by' <- ]" :=
  (DirLimitLinear.dirlim_lmodMixin (Phant U))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_linear := DirLimitLinear.dlinj_linear.
Canonical dlind_linear := DirLimitLinear.dlind_linear.


Module DirLimitLalg.
Section DirLimitLalg.

Variables (disp : unit) (I : dirType disp).
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob i) -> (Ob j) }.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b c : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_lmodType :=
  Eval hnf in LmodType R TLim [lmodMixin of TLim by <-].

Fact dlscaleAl r a b : r *: (a * b) = r *: a * b.
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearZ /= -!rmorphM /= -linearZ /= -scalerAl.
Qed.
Definition dirlim_lalgMixin of phant TLim := dlscaleAl.
Local Canonical dirlim_lalgType := Eval hnf in LalgType R TLim dlscaleAl.

Canonical dlinj_lrmorphism i : {lrmorphism Ob i -> TLim} :=
  AddLRMorphism (DirLimitLinear.dlinj_is_linear TLim (i := i)).

Section UniversalProperty.

Variable (T : lalgType R) (f : forall i, {lrmorphism (Ob i) -> T }).
Hypothesis Hcomp : iscompat Sys f.
Canonical dlind_lrmorphism : {lrmorphism TLim -> T} :=
  AddLRMorphism (DirLimitLinear.dlind_is_linear Hcomp).

End UniversalProperty.

End DirLimitLalg.
End DirLimitLalg.

Notation "[ 'lalgMixin' 'of' U 'by' <- ]" :=
  (DirLimitLalg.dirlim_lalgMixin (Phant U))
  (at level 0, format "[ 'lalgMixin'  'of'  U  'by'  <- ]") : form_scope.

Canonical dlinj_lrmorphism := DirLimitLalg.dlinj_lrmorphism.
Canonical dlind_lrmorphism := DirLimitLalg.dlind_lrmorphism.


Module DirLimitAlg.
Section DirLimitAlg.

Variables (disp : unit) (I : dirType disp).
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.
Implicit Type (a b : TLim) (r : R).

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_lmodType :=
  Eval hnf in LmodType R TLim [lmodMixin of TLim by <-].
Local Canonical dirlim_lalgType :=
  Eval hnf in LalgType R TLim [lalgMixin of TLim by <-].

Fact dlscaleAr r a b : r *: (a * b) = a * (r *: b).
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
by rewrite -linearZ /= -!rmorphM /= -linearZ /= -scalerAr.
Qed.
Definition dirlim_algMixin of phant TLim := dlscaleAr.
Canonical dirlim_algType := Eval hnf in AlgType R TLim dlscaleAr.

End DirLimitAlg.
End DirLimitAlg.

Notation "[ 'algMixin' 'of' U 'by' <- ]" :=
  (DirLimitAlg.dirlim_algMixin (Phant U))
  (at level 0, format "[ 'algMixin'  'of'  U  'by'  <- ]") : form_scope.


Module DirLimitField.
Section DirLimitField.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob i) -> (Ob j)}.
Variable Sys : dirsys bonding.

Variable TLim : dirLimType Sys.

Local Canonical TLim_zmodType :=
  Eval hnf in ZmodType TLim [zmodMixin of TLim by <-].
Local Canonical TLim_ringType :=
  Eval hnf in RingType TLim [ringMixin of TLim by <-].
Local Canonical TLim_unitRingType :=
  Eval hnf in UnitRingType TLim [unitRingMixin of TLim by <-].
Local Canonical TLim_comRingType :=
  Eval hnf in ComRingType TLim [comRingMixin of TLim by <-].
Local Canonical dirlim_comUnitRingType := Eval hnf in [comUnitRingType of TLim].
Local Canonical TLim_idomainType :=
  Eval hnf in IdomainType TLim [idomainMixin of TLim by <-].

Fact dirlim_fieldMixin of phant TLim :
  GRing.Field.mixin_of [unitRingType of TLim].
Proof.
move=> a.
case: (dlrepr a) (dlreprP a) => /= ia xa <-{a} Hxa.
have : xa != 0 by move: Hxa; apply contra => /eqP ->; rewrite raddf0.
rewrite -unitfE => Ha.
by apply/dlunitP; exists ia; exists xa.
Qed.

End DirLimitField.
End DirLimitField.

Notation "[ 'fieldMixin' 'of' U 'by' <- ]" :=
  (DirLimitField.dirlim_fieldMixin (Phant U))
  (at level 0, format "[ 'fieldMixin'  'of'  U  'by'  <- ]") : form_scope.

Close Scope ring_scope.



(***************************************************************************)
(** A default implementation for direrct limits                            *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Record dirlim := DirLim {
                     dlpair :> {i & Ob i};
                     _ : dlcanon bonding dlpair == dlpair;
                   }.

Definition dirlim_of of phantom (dirsys bonding) Sys := dirlim.
Identity Coercion type_dirlim_of : dirlim_of >-> dirlim.

Local Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).


Canonical dirlim_eqType := EqType dirlim gen_eqMixin.
Canonical dirlimp_eqType := EqType {dirlim Sys} gen_eqMixin.
Canonical dirlim_choiceType := ChoiceType dirlim gen_choiceMixin.
Canonical dirlimp_choiceType := ChoiceType {dirlim Sys} gen_choiceMixin.
Canonical dirlimp_subType := [subType for dlpair].

End Implem.
Notation "{ 'dirlim' S }" := (dirlim_of (Phantom _ S)).

(*
Section DirectLimitTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.

Variable Sys : dirsys bonding.
Implicit Type x y : {dirlim Sys}.

Definition dlinj_impl i : {dirlim Sys} -> Ob i :=
  (dirlimthr (Sys := Sys))^~ i.

Lemma dlinj_implE x :
  forall i j, forall (Hij : i <= j),
      bonding Hij (dlinj_impl j x) = dlinj_impl i x.
Proof. by case: x => [thr /asboolP] /=. Qed.

Lemma dlinj_implP : iscompat Sys dlinj_impl.
Proof. by move=> i j Hij [thr /asboolP] /=. Qed.

Local Notation "''pi_' i" := (dlinj_impl i).

Lemma dirlimP x y : (forall i, 'pi_i x = 'pi_i y) -> x = y.
Proof.
move=> eqxy; apply val_inj => /=.
case: x y eqxy => [fx _] [fy _] /=.
exact: functional_extensionality_dep.
Qed.

(** Budlding the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Ob i -> T).
Hypothesis Hcomp : iscompat Sys f.

Fact dlind_spec :
  { dlind : T -> dirlim Sys | forall i, 'pi_i \o dlind = f i }.
Proof.
move: Hcomp; rewrite /iscompat => Hf; pose fdl t i := f i t.
have Hfdl t : isthread Sys (fdl t) by rewrite /fdl=> i j Hij; apply Hf.
by exists (fun t => MkDirLim (Hfdl t)).
Qed.
Definition dlind_impl := let: exist f _ := dlind_spec in f.
Lemma dlind_implP i t : 'pi_i (dlind_impl t) = f i t.
Proof.
rewrite /dlind_impl; move: t; case: dlind_spec => un Hun t.
by rewrite -Hun.
Qed.

Lemma dlind_implE (un : T -> dirlim Sys) :
  (forall i, 'pi_i \o un =1 f i) -> un =1 dlind_impl.
Proof.
move=> H x; apply dirlimP => i.
by rewrite -/(('pi_i \o un) _) H dlind_implP.
Qed.

End UniversalProperty.

End DirerseLimitTheory.


Section InterSpec.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, (i <= j)%O -> Ob j -> Ob i.
Variable Sys : dirsys bonding.

Program Definition dirlim_Mixin :=
  @DirLimMixin disp I Ob bonding Sys {dirlim Sys}
               (dlinj_impl (Sys := Sys)) (dlind_impl (Sys := Sys)) _ _ _.
Next Obligation. by move=> i j Hij x; apply: dlinj_implE. Qed.
Next Obligation. by move=> x /=; rewrite dlind_implP. Qed.
Next Obligation. by move=> x; apply: (dlind_implE Hcomp). Qed.
Canonical dirlim_dirlimType := DirLimType {dirlim Sys} dirlim_Mixin.

End InterSpec.


Open Scope ring_scope.
Section Canonicals.

Variables (disp : unit) (I : dirType disp).

Section ZModule.
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob j -> Ob i}.
Variable Sys : dirsys bonding.
Canonical dirlim_zmodType :=
  Eval hnf in ZmodType {dirlim Sys} [zmodMixin of {dirlim Sys} by <-].
End ZModule.

Section Ring.
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_ringType :=
  Eval hnf in RingType {dirlim Sys} [ringMixin of {dirlim Sys} by <-].
End Ring.

Section ComRing.
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_comRingType :=
  Eval hnf in ComRingType {dirlim Sys} [comRingMixin of {dirlim Sys} by <-].
End ComRing.

Section UnitRing.
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_unitRingType :=
  Eval hnf in UnitRingType {dirlim Sys} [unitRingMixin of {dirlim Sys} by <-].
End UnitRing.

Section ComUnitRing.
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlimp_comUnitRingType := [comUnitRingType of {dirlim Sys}].
End ComUnitRing.

Section IDomain.
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_idomainType :=
  Eval hnf in IdomainType {dirlim Sys} [idomainMixin of {dirlim Sys} by <-].
End IDomain.

Section Linear.
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_lmodType :=
  Eval hnf in LmodType R {dirlim Sys} [lmodMixin of {dirlim Sys} by <-].
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_lalgType :=
  Eval hnf in LalgType R {dirlim Sys} [lalgMixin of {dirlim Sys} by <-].
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_algType :=
  Eval hnf in AlgType R {dirlim Sys} [algMixin of {dirlim Sys} by <-].
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlimp_unitAlgType := [unitAlgType R of {dirlim Sys}].
End UnitAlg.

Section Field.
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.
Canonical dirlim_fieldType :=
  Eval hnf in FieldType {dirlim Sys} [fieldMixin of {dirlim Sys} by <-].
End Field.

End Canonicals.


Section Test.
Variable (R : comRingType).
Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob j -> Ob i}.
Variable Sys : dirsys bonding.
Let test := [algType R of {dirlim Sys}].
End Test.


(***************************************************************************)
(** Valuation in direrse limits                                            *)
(***************************************************************************)
Section Valuation.

Variable Ob : nat -> zmodType.
Variable bonding : forall i j : nat, (i <= j)%O -> {additive (Ob j) -> (Ob i)}.
Variable Sys : dirsys bonding.

Implicit Type (x y : {dirlim Sys}).


Definition valuat x : natbar :=
  if altP (x =P 0) is AltFalse Pf then Nat (ex_minn (dl_neq0 Pf))
  else Inf.

Variant valuat_spec x : natbar -> Type :=
  | ValNat n of 'pi_n x != 0 & (forall i, (i < n)%N -> 'pi_i x = 0) :
      valuat_spec x (Nat n)
  | ValInf of x = 0 : valuat_spec x Inf.

Lemma valuatP x : valuat_spec x (valuat x).
Proof.
rewrite /valuat; case (altP (x =P 0)) => [Pf|NPf]; first exact: ValInf.
case: ex_minnP => v Hv vmin; apply ValNat => [|i iv]; first exact: Hv.
by apply/contraTeq: iv; rewrite -leqNgt; apply vmin.
Qed.

Lemma lt_valuatP x n : reflect ('pi_n x = 0) (Nat n < valuat x)%O.
Proof.
apply (iffP idP); case: valuatP => [v Hv vmin /= |->].
- by rewrite ltEnatbar; apply vmin.
- by rewrite raddf0.
- apply contra_eqT; rewrite ltEnatbar -leqNgt => vlen.
  apply/contra: Hv => /eqP/(congr1 (bonding vlen)).
  by rewrite (dlinjE x) raddf0 => ->.
- by [].
Qed.

Lemma le_valuatP x n :
  reflect (forall i, (i < n)%N -> 'pi_i x = 0) (Nat n <= valuat x)%O.
Proof.
apply (iffP idP).
- case: valuatP => [v Hv vmin /= |-> _ i _].
  + by rewrite leEnatbar => nlev i /leq_trans/(_ nlev); apply vmin.
  + by rewrite raddf0.
- case: n => // n; first exact: le0bar.
  move=> /(_ n)/(_ (ltnSn _)) /lt_valuatP.
  by case: (valuat x)=> // v; rewrite ltEnatbar leEnatbar.
Qed.

Lemma proj_gt_valuat x n : (Nat n >= valuat x)%O = ('pi_n x != 0).
Proof. by apply negb_inj; rewrite negbK -ltNge; apply/lt_valuatP/eqP. Qed.

Lemma valuatNatE x n :
  'pi_n x != 0 -> (forall i, (i < n)%N -> 'pi_i x = 0) -> valuat x = Nat n.
Proof.
move=> Hn nmin; apply le_anti; rewrite proj_gt_valuat Hn /=.
exact/le_valuatP.
Qed.

Lemma valuat0 : valuat 0 = Inf.
Proof. by case: valuatP => [v | //]; rewrite raddf0 eqxx. Qed.

Lemma valuat0P x : (valuat x == Inf) = (x == 0).
Proof.
apply/eqP/eqP=> [valx|->]; last exact: valuat0.
by apply/dirlimE=> i; rewrite raddf0; apply/lt_valuatP; rewrite valx.
Qed.

Lemma valuatN x : valuat (- x) = valuat x.
Proof.
case: (valuatP x) => [vN HvN vnmiN /= | ->]; last by rewrite oppr0 valuat0.
apply valuatNatE; first by rewrite raddfN oppr_eq0.
by move=> i /vnmiN; rewrite raddfN /= => ->; rewrite oppr0.
Qed.

Lemma valuatD x1 x2 :
  (valuat x1 `&` valuat x2 <= valuat (x1 + x2))%O.
Proof.
wlog v1lev2 : x1 x2 / (valuat x1 <= valuat x2)%O.
  move=> Hlog; case (leP (valuat x1) (valuat x2)) => [|/ltW]/Hlog //.
  by rewrite addrC meetC.
rewrite (meet_idPl v1lev2); move: v1lev2.
case: (valuatP x1)=> [v1 Hv1 v1min|->]; last by rewrite add0r.
case: (valuatP x2)=> [v2 Hv2 v2min|->]; last by rewrite addr0 (valuatNatE Hv1).
rewrite leEnatbar => le12.
apply/le_valuatP => i Hi; rewrite raddfD /= v1min ?v2min ?addr0 //.
exact: leq_trans Hi le12.
Qed.
Lemma valuat_sum I r P (F : I ->  {dirlim Sys}) :
  (\meet_(i <- r | P i) valuat (F i) <= valuat (\sum_(i <- r | P i) F i))%O.
Proof.
apply: (big_ind2 (fun x v => v <= valuat x)%O); rewrite ?valuat0 //=.
by move=> x1 v1 x2 v2 H1 H2; apply: (le_trans (leI2 _ _) (valuatD x1 x2)).
Qed.

Lemma valuatB s1 s2 :
  (valuat s1 `&` valuat s2 <= valuat (s1 - s2))%O.
Proof. by have:= valuatD s1 (-s2); rewrite valuatN. Qed.

Lemma valuatDr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 + s2) = valuat s1.
Proof.
case: (valuatP s2) => [v2 _   v2min|-> _]; last by rewrite addr0.
case: (valuatP s1) => [v1 Hv1 v1min|->]; last by rewrite ltIbar.
rewrite ltEnatbar => v12.
apply valuatNatE=> [|n nv1]; rewrite raddfD /= v2min ?addr0 // ?v1min //.
exact: ltn_trans nv1 v12.
Qed.

Lemma valuatBr s1 s2 :
  (valuat s1 < valuat s2)%O -> valuat (s1 - s2) = valuat s1.
Proof. by rewrite -(valuatN s2) => /valuatDr. Qed.
Lemma valuatBl s1 s2 :
  (valuat s2 < valuat s1)%O -> valuat (s1 - s2) = valuat s2.
Proof. by rewrite -(valuatN s2) addrC => /valuatDr. Qed.

End Valuation.

(*
From mathcomp Require Import finmap.

Section CommHugeOp.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> eqType.
Variable bonding : forall i j : I, (i <= j)%O -> (Ob j) -> (Ob i).
Variable Sys : dirsys bonding.

Variable (C : choiceType).
Variables (idx : {dirlim Sys}) (op : Monoid.com_law idx).

Implicit Type F : C -> {dirlim Sys}.
Implicit Types (x y z t : {dirlim Sys}).

Definition invar i x := forall s, 'pi_i (op x s) = 'pi_i s.
Definition is_dlopable F :=
  forall i, exists s : seq C, forall c, c \notin s -> invar i (F c).
Lemma dlopable_spec F :
  is_dlopable F ->
  forall i, { f : {fset C} | f =i predC (fun c => `[< invar i (F c)>]) }.
Proof.
move=> H i; move/(_ i): H => /cid [s Hs].
have key : unit by [].
exists (seq_fset key [seq c <- s | ~~ `[< invar i (F c)>]]) => c.
rewrite seq_fsetE !inE mem_fdlter.
by case: (boolP `[< _>]) => //=; apply contraR => /Hs/asboolT.
Qed.
Definition dlopable F (sm : is_dlopable F) c :=
  let: exist fs _ := dlopable_spec sm c in fs.

Lemma dlopableP F (sm : is_dlopable F) i c :
  reflect (invar i (F c)) (c \notin (dlopable sm i)).
Proof.
rewrite /dlopable; apply (iffP negP); case: dlopable_spec => f Hf.
- by rewrite Hf inE => /negP; rewrite negbK => /asboolW.
- by rewrite Hf inE => H; apply/negP; rewrite negbK; apply asboolT.
Qed.

Lemma dlopable_subset F (sm : is_dlopable F) i j :
  (i <= j)%O -> (dlopable sm i `<=` dlopable sm j)%fset.
Proof.
move=> dlej.
apply/fsubsetP => c; apply/contraLR => /dlopableP Hdir.
by apply/dlopableP => x; rewrite -!(dlinjE _ dlej) Hdir.
Qed.

Fact dlopable_istrhead F (sm : is_dlopable F) :
  isthread Sys (fun i => 'pi_i (\big[op/idx]_(c <- dlopable sm i) F c)).
Proof.
move=> i j Hij; rewrite dlinjE.
rewrite (bigID (fun c => `[< invar i (F c)>])) /=.
set X := (X in op _ X); set Y := (Y in _ = _ Y).
have {X} -> : X = Y.
  rewrite {}/X {}/Y; apply eq_fbigl_cond => c.
  rewrite !inE andbT; apply negb_inj; rewrite negb_and negbK.
  case: (boolP (c \in (dlopable sm j))) => /= Hc.
  - by apply/asboolP/idP=> /dlopableP //; apply.
  - suff -> : c \notin (dlopable sm i) by [].
    by apply/contra: Hc; apply: (fsubsetP (dlopable_subset sm Hij)).
elim: (X in \big[op/idx]_(i <- X | _) _) => [| s0 s IHs].
  by rewrite big_ndl Monoid.mul1m.
rewrite big_cons /=; case: asboolP => [|]; last by rewrite IHs.
by rewrite -Monoid.mulmA {1}/invar => ->.
Qed.

Definition HugeOp F : {dirlim Sys} :=
  if pselect (is_dlopable F) is left sm
  then MkDirLim (dlopable_istrhead sm)
  else idx.

Local Notation "\Op_( c ) F" := (HugeOp (fun c => F)) (at level 0).

(*
Lemma coefsHugeOp F i (S : {fset C}) :
  is_dlopable F ->
  subpred (predC (mem S)) (fun c => `[< invar i (F c)>]) ->
  'pi_i (\Op_( c ) (F c)) = 'pi_i (\big[op/idx]_(c <- S) (F c)).
Proof.
rewrite /HugeOp=> Hop Hsub; case: pselect; last by move=> /(_ Hop).
move=> /= {Hop} Hop.
transitivity ('pi_i (\big[op/idx]_(c <- S | c \in dlopable Hop i) F c));
  first last.
  

rewrite [in RHS](bigID [pred c | `[< invar i (F c)>]]) /=.
  rewrite [X in op _ X]big1 ?addr0; first last.
  move=> j /andP [].

   rewrite negbK => /eqP.
rewrite -[RHS]big_fdlter; apply: perm_big.
apply: (uniq_perm (fset_uniq _) (fdlter_uniq _ (enum_finpred_uniq _))) => i.
rewrite dlopableE mem_filter inE enum_finpredE.
 by case: (boolP (_ == 0)) => // /Hsub /= ->.
Qed.
 *)

End CommHugeOp.
*)
*)

