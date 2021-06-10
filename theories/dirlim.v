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

Definition cocone of dirsys := fun T (mors : forall i, Ob i -> T) =>
  forall i j, forall (Hij : i <= j), mors j \o bonding Hij =1 mors i.

Lemma coconeE Sys T (mors : forall i, Ob i -> T) : cocone Sys mors ->
  forall i j (Hij : i <= j) x,
  mors j (bonding Hij x) = mors i x.
Proof. by rewrite /cocone => H i j le_ij x; rewrite -(H i j le_ij). Qed.

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
      (cocone Sys f) -> TLim -> T;
  _ : cocone Sys dirlim_inj;
  _ : forall (T : Type) (f : forall i, Ob i -> T) (Hcone : cocone Sys f),
      forall i, dirlim_ind Hcone \o @dirlim_inj i =1 f i;
  _ : forall (T : Type) (f : forall i, Ob i -> T) (Hcone : cocone Sys f),
      forall (ind : TLim -> T),
        (forall i, ind \o @dirlim_inj i =1 f i) ->
        ind =1 dirlim_ind Hcone
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

Lemma inj_cocone : cocone Sys \inj.
Proof. by rewrite /inj_phant; case: dlT => /= [TLim [eqM []]]. Qed.

Lemma ind_commute T (f : forall i, Ob i -> T) (Hcone : cocone Sys f) :
  forall i, \ind Hcone \o \inj_ i =1 f i.
Proof. by rewrite /inj_phant /ind_phant; case: dlT => /= [TLim [eqM []]]. Qed.

Lemma injindE  T (f : forall i, Ob i -> T) (Hcone : cocone Sys f) i x :
  (\ind Hcone) (\inj_ i x) = f i x.
Proof. exact: ind_commute. Qed.

Lemma ind_uniq T (f : forall i, Ob i -> T) (Hcone : cocone Sys f) :
  forall (ind : dlT -> T),
    (forall i, ind \o \inj_ i =1 f i) -> ind =1 \ind Hcone.
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


Inductive dlcongr i j (x : Ob i) (y : Ob j) : Prop :=
  | DLCongr : forall k (le_ik : i <= k) (le_jk : j <= k),
              (bonding le_ik x = bonding le_jk y) -> dlcongr x y.
Arguments DLCongr {i j x y k} (le_ik le_jk).

Lemma dlcongr_bonding i j (le_ij : i <= j) (x : Ob i) :
  dlcongr x (bonding le_ij x).
Proof.
apply: (DLCongr le_ij (lexx j)).
by rewrite bonding_transE //; apply: bondingE.
Qed.

Lemma dlcongr_refl i (x : Ob i) : dlcongr x x.
Proof. exact: DLCongr. Qed.
Lemma dlcongr_sym_impl i j (x : Ob i) (y : Ob j) : dlcongr x y -> dlcongr y x.
Proof.
move=> [k le_ik le_jk Hbond].
by apply: (DLCongr le_jk le_ik); rewrite Hbond.
Qed.
Lemma dlcongr_sym i j (x : Ob i) (y : Ob j) : dlcongr x y = dlcongr y x.
Proof. by rewrite propeqE; split; apply: dlcongr_sym_impl. Qed.
Lemma dlcongr_trans i j k (x : Ob i) (y : Ob j) (z : Ob k) :
  dlcongr x y -> dlcongr y z -> dlcongr x z.
Proof.
move=> [l le_il le_jl Hxy].
move=> [m le_jm le_km Hyz].
have [n le_ln le_mn] := directedP l m.
apply: (DLCongr (le_trans le_il le_ln) (le_trans le_km le_mn)).
rewrite -!bonding_transE // {}Hxy -{}Hyz !bonding_transE //.
exact: bondingE.
Qed.

Lemma cocone_dlcongr i (x : Ob i) :
  cocone Sys (fun j (y : Ob j) => `[< dlcongr x y >]).
Proof.
move=> j k le_jk y /=.
case: (boolP `[< dlcongr x y >]) => [Hthr | Hnthr].
- move: Hthr => /asboolP [l le_il le_jl Hbond]; apply/asboolP.
  have [m le_km le_lm] := directedP k l.
  apply: (DLCongr (le_trans le_il le_lm) le_km).
  rewrite -(dirsys_comp Sys le_il le_lm) /= Hbond.
  by rewrite !bonding_transE //; apply: bondingE.
- apply/negP => /= /asboolP [l le_il le_kl].
  rewrite bonding_transE // => Hbond.
  move: Hnthr => /asboolP; apply.
  exact: (DLCongr le_il (le_trans le_jk le_kl)).
Qed.

Section Compatibility.

Variables (T : Type) (f : forall i, Ob i -> T).
Hypothesis Hcone : cocone Sys f.

Lemma dlcongrE i j (x : Ob i) (y : Ob j) : dlcongr x y -> f x = f y.
Proof.
move=> [k le_ik le_jk Hbond].
by rewrite -(coconeE Hcone le_ik) Hbond (coconeE Hcone).
Qed.

End Compatibility.


Variable TLim : dirLimType Sys.

Lemma dirlimP (t : TLim) : exists k (y : Ob k), 'inj y = t.
Proof.
rewrite not_existsP => H.
pose f i := pred0 (T := Ob i).
have Hcone : cocone Sys f by [].
have /(ind_uniq Hcone)/(_ t) :
  forall i, (pred0 (T := TLim)) \o 'inj =1 f i by [].
suff /(ind_uniq Hcone)/(_ t) <- : forall i, (pred1 t) \o 'inj =1 f i.
  by rewrite /= eqxx.
rewrite /f => i x /=; apply/negP => /eqP eq_inj.
by apply/(H i); exists x.
Qed.

Lemma dirlim_pairP (t : TLim) : { p : {i & Ob i} | 'inj (projT2 p) = t }.
Proof.
by apply cid; case: (dirlimP t) => i [x eqinj]; exists (existT _ i x).
Qed.

End DirLimitCongr.
Arguments DLCongr {disp I Ob bonding i j x y k} (le_ik le_jk).


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

Lemma dlcanon_id p : dlcanon (dlcanon p) = dlcanon p.
Proof. by apply dlcanonE; rewrite dlcongr_sym; apply: dlcanonP. Qed.

Variable TLim : dirLimType Sys.
Implicit Types (t a b c : TLim).

Lemma dirlimEI (i : I) (x : Ob i) (y : Ob i) :
  'inj[TLim] x = 'inj[TLim] y ->
  exists (k : I) (le_ik : i <= k), bonding le_ik x = bonding le_ik y.
Proof.
move => Heq; apply contrapT; rewrite -forallNP => Hbond.
have Hcone := cocone_dlcongr Sys y.
have:= injindE TLim Hcone y; rewrite -Heq injindE.
have /asboolP -> := dlcongr_refl bonding y.
move=> /asboolP [j le_ij le_ij2] Habs.
apply: (Hbond j); exists (le_ij); rewrite Habs.
exact: bondingE.
Qed.

Lemma dirlimE (i j : I) (x : Ob i) (y : Ob j) :
  ('inj[TLim] x = 'inj[TLim] y) <-> (dlcongr bonding x y).
Proof.
split => [H | [k le_ik le_jk Hbond]].
- have [l le_il le_jl] := directedP i j.
  have /dirlimEI [k [le_lk]] :
      'inj[TLim] (bonding le_il x) = 'inj[TLim] (bonding le_jl y).
    have /= -> := (inj_cocone TLim le_il x).
    by rewrite H -(inj_cocone TLim le_jl y).
  rewrite !bonding_transE // => Hk.
  exact: (DLCongr (le_trans le_il le_lk) (le_trans le_jl le_lk)).
- have /= <- := (inj_cocone TLim le_ik x).
  by rewrite Hbond -(inj_cocone TLim le_jk y).
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
by split; have /= -> := (inj_cocone TLim) _ _ _ _.
Qed.
Lemma get_repr3 a b c :
  exists i (x y z : Ob i), [/\ 'inj x = a, 'inj y = b & 'inj z = c].
Proof.
case: (get_repr2 a b) => i [x] [y] [<-{a} <-{b}].
case: (dlrepr c) (dlreprP c) => /= j z <-{c}.
case: (directedP i j) => n le_in le_jn.
exists n; exists (bonding le_in x); exists (bonding le_in y);
  exists (bonding le_jn z).
by split; have /= -> := (inj_cocone TLim) _ _ _ _.
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
Variable bonding : forall i j, (i <= j)%O -> {additive Ob i -> Ob j}.
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
by apply (DLCongr le_j le_ij); rewrite !raddf0.
Qed.
Lemma dloppE i (x : Ob i) : dlopp ('inj x) = 'inj (-x).
Proof.
rewrite /dlzero dirlimE.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra.
rewrite dirlimE => [[j le_iaj le_ij Hbond]].
by apply: (DLCongr le_iaj le_ij); rewrite !raddfN Hbond.
Qed.
Lemma dladdE i (x : Ob i) (y : Ob i) : dladd ('inj x) ('inj y) = 'inj (x + y).
Proof.
rewrite /dladd.
case: (dlrepr ('inj[TLim] x)) (dlreprP ('inj[TLim] x)) => /= ia ra Hra.
case: (dlrepr ('inj[TLim] y)) (dlreprP ('inj[TLim] y)) => /= ib rb Hrb.
case: directedP => m le_iam le_ibm.
move: Hra; rewrite dirlimE => [[ja le_iaja le_ija Hbonda]].
move: Hrb; rewrite dirlimE => [[jb le_ibjb le_ijb Hbondb]].
case: (directedP ja jb) => n le_jan le_jbn.
case: (directedP m n) => bnd le_mbnd le_nbnd.
rewrite dirlimE.
apply: (DLCongr le_mbnd (le_trans le_ija (le_trans le_jan le_nbnd))).
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
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_additive : additive (\ind Hcone).
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
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
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
by apply: (DLCongr le_j le_ij); rewrite !rmorph1.
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
move: Hra; rewrite dirlimE => [[ja le_iaja le_ija Hbonda]].
move: Hrb; rewrite dirlimE => [[jb le_ibjb le_ijb Hbondb]].
case: (directedP ja jb) => n le_jan le_jbn.
case: (directedP m n) => bnd le_mbnd le_nbnd.
rewrite dirlimE.
apply: (DLCongr le_mbnd (le_trans le_ija (le_trans le_jan le_nbnd))).
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
rewrite dirlimE => [[i le1 le2]].
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
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_multiplicative : multiplicative (\ind Hcone).
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
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
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
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
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
rewrite dirlimE => [[il le_i_il le_il Hl]].
rewrite dirlimE => [[ir le_i_ir le_ir Hr]].
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
  by rewrite /bu; have /= -> := inj_cocone TLim _ u.
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
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
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
rewrite dirlimE => [[l le_il le_i0l]].
rewrite !rmorphM !rmorph0 {le_i0l i0} => /eqP.
by rewrite mulf_eq0 => /orP [] /eqP /(congr1 'inj[TLim]) H; [left|right];
   move: H; have /= -> := inj_cocone TLim _ _ => ->; rewrite rmorph0.
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
Variable bonding : forall i j, (i <= j)%O -> {linear Ob i -> Ob j}.
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
rewrite dirlimE => [[j le_iaj le_ij Hbond]].
by exists j le_iaj le_ij; rewrite !linearZ Hbond.
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
Hypothesis Hcone : cocone Sys f.

Fact dlind_is_linear : linear (\ind Hcone).
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
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j }.
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
Hypothesis Hcone : cocone Sys f.
Canonical dlind_lrmorphism : {lrmorphism TLim -> T} :=
  AddLRMorphism (DirLimitLinear.dlind_is_linear Hcone).

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
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j}.
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
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
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
(** A default implementation for direct limits                             *)
(*                                                                         *)
(***************************************************************************)
Section Implem.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Record dirlim := DirLim {
                     dlpair : {i & Ob i};
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


Section DirectLimitTheory.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, i <= j -> Ob i -> Ob j.

Variable Sys : dirsys bonding.
Implicit Type (i j k : I) (a b : {dirlim Sys}).

Definition dlinj_fun i (x : Ob i) := dlcanon bonding (existT _ i x).
Lemma dlinj_spec i (x : Ob i) : dlcanon bonding (dlinj_fun x) == dlinj_fun x.
Proof. by rewrite /dlinj_fun dlcanon_id. Qed.
Definition dlinj i (x : Ob i) : {dirlim Sys} := DirLim (dlinj_spec x).

Lemma dlinjP i (x : Ob i) : dlcongr bonding x (projT2 (dlpair (dlinj x))).
Proof.
rewrite /dlinj /= /dlinj_fun /=.
exact: (dlcanonP bonding (existT _ i x)).
Qed.

Local Notation "''inj_' i" := (@dlinj i).

(** Budlding the universal induced map *)
Section UniversalProperty.

Variable (T : Type) (f : forall i, Ob i -> T).

Definition dlind of cocone Sys f := fun a => f (projT2 (dlpair a)).

Hypothesis Hcone : cocone Sys f.

Lemma dlindP i (x : Ob i) : dlind Hcone ('inj_i x) = f x.
Proof.
rewrite /dlind; apply (dlcongrE Hcone).
by rewrite dlcongr_sym; apply: (dlinjP x).
Qed.

Lemma dlindE i j (x : Ob i) (y : Ob j) :
  dlcongr bonding x y -> dlind Hcone ('inj_i x) = dlind Hcone ('inj_j y).
Proof. by rewrite !dlindP => /(dlcongrE Hcone). Qed.

End UniversalProperty.

End DirectLimitTheory.


Section InterSpec.

Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> choiceType.
Variable bonding : forall i j, (i <= j)%O -> Ob i -> Ob j.
Variable Sys : dirsys bonding.

Program Definition dirlim_Mixin :=
  @DirLimMixin disp I Ob bonding Sys {dirlim Sys}
               (dlinj Sys) (dlind (Sys := Sys)) _ _ _.
Next Obligation.
move=> i j le_ij x /=; apply val_inj => /=.
rewrite /dlinj_fun /= -(dlcanonE Sys) /= dlcongr_sym.
exact: dlcongr_bonding.
Qed.
Next Obligation. by move=> x /=; rewrite dlindP. Qed.
Next Obligation.
move=> [[i x] /= Hx].
suff -> : (DirLim Hx) = dlinj Sys x by rewrite dlindP -(H i x).
by apply val_inj => /=; rewrite /dlinj_fun (eqP Hx).
Qed.
Canonical dirlim_dirlimType := DirLimType {dirlim Sys} dirlim_Mixin.

End InterSpec.


Open Scope ring_scope.
Section Canonicals.

Variables (disp : unit) (I : dirType disp).

Section ZModule.
Variable Ob : I -> zmodType.
Variable bonding : forall i j, (i <= j)%O -> {additive Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_zmodType :=
  Eval hnf in ZmodType {dirlim Sys} [zmodMixin of {dirlim Sys} by <-].
End ZModule.

Section Ring.
Variable Ob : I -> ringType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_ringType :=
  Eval hnf in RingType {dirlim Sys} [ringMixin of {dirlim Sys} by <-].
End Ring.

Section ComRing.
Variable Ob : I -> comRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_comRingType :=
  Eval hnf in ComRingType {dirlim Sys} [comRingMixin of {dirlim Sys} by <-].
End ComRing.

Section UnitRing.
Variable Ob : I -> unitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_unitRingType :=
  Eval hnf in UnitRingType {dirlim Sys} [unitRingMixin of {dirlim Sys} by <-].
End UnitRing.

Section ComUnitRing.
Variable Ob : I -> comUnitRingType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlimp_comUnitRingType := [comUnitRingType of {dirlim Sys}].
End ComUnitRing.

Section IDomain.
Variable Ob : I -> idomainType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_idomainType :=
  Eval hnf in IdomainType {dirlim Sys} [idomainMixin of {dirlim Sys} by <-].
End IDomain.

Section Linear.
Variables (R : ringType).
Variable Ob : I -> lmodType R.
Variable bonding : forall i j, (i <= j)%O -> {linear Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_lmodType :=
  Eval hnf in LmodType R {dirlim Sys} [lmodMixin of {dirlim Sys} by <-].
End Linear.

Section Lalg.
Variables (R : ringType).
Variable Ob : I -> lalgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_lalgType :=
  Eval hnf in LalgType R {dirlim Sys} [lalgMixin of {dirlim Sys} by <-].
End Lalg.

Section Alg.
Variables (R : comRingType).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_algType :=
  Eval hnf in AlgType R {dirlim Sys} [algMixin of {dirlim Sys} by <-].
End Alg.

Section UnitAlg.
Variables (R : comRingType).
Variable Ob : I -> unitAlgType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlimp_unitAlgType := [unitAlgType R of {dirlim Sys}].
End UnitAlg.

Section Field.
Variable Ob : I -> fieldType.
Variable bonding : forall i j, (i <= j)%O -> {rmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Canonical dirlim_fieldType :=
  Eval hnf in FieldType {dirlim Sys} [fieldMixin of {dirlim Sys} by <-].
End Field.

End Canonicals.


Section Test.
Variable (R : comRingType).
Variables (disp : unit) (I : dirType disp).
Variable Ob : I -> algType R.
Variable bonding : forall i j, (i <= j)%O -> {lrmorphism Ob i -> Ob j}.
Variable Sys : dirsys bonding.
Let test := [algType R of {dirlim Sys}].
End Test.
