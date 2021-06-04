(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype.
From mathcomp Require Import div tuple bigop ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Fact aux_equivb (P : Prop) (b c : bool) : reflect P b -> b = c -> reflect P c.
Proof. by move => reflect_P_b b_eq_c ; rewrite b_eq_c in reflect_P_b. Qed.

Section MoreNatTheory.

Lemma lt_predn n : (n.-1 < n) = (n != 0).
Proof. by case: n => [//|n]; rewrite ltnSn. Qed.

Fact n_eq1 n : n != 0 -> n < 2 -> n = 1.
Proof. by case: n => [?|[?|[]]]. Qed.

Fact leq_npred m n : m > 0 -> (m <= n.-1) = (m < n).
Proof. by move: m n => [|m] [|n]. Qed.

Fact predn_sub m n : (m - n).-1 = (m.-1 - n).
Proof. by case: m => //= m; rewrite subSKn. Qed.

Lemma geq_subn m n : m <= n -> m - n = 0.
Proof. by rewrite -subn_eq0 => /eqP. Qed.

Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. by case: p => // p _; rewrite addnS !ltnS leq_subLR. Qed.

Lemma leq_subRL m n p : 0 < n -> (n <= p - m) = (m + n <= p).
Proof. by case: n => // n _; rewrite addnS ltn_subRL. Qed.

Fact ltpredn a b c : a != 0 -> ((a + b).-1 < c + b) = (a.-1 < c).
Proof. by rewrite -lt0n => a_gt0; rewrite !prednK ?ltn_addr // leq_add2r. Qed.

Lemma leq_leq_subRL m n p : m <= p -> (n <= p - m) = (m + n <= p).
Proof. by move=> ?; case: n => [|n]; rewrite ?leq0n ?addn0 ?leq_subRL. Qed.

Lemma leq_ltn_subLR m n p : n <= m -> (m - n < p) = (m < n + p).
Proof.
move=> le_nm; case: p => [|p]; last by rewrite ltn_subLR.
by rewrite addn0 ltn0 ltnNge le_nm.
Qed.

Lemma ltnpredn m n : (m < n.-1) = (m.+1 < n).
Proof. by case: n => [//|n]; rewrite succnK. Qed.

Lemma ltn_subCl m n p : 0 < p -> 0 < n -> (m - n < p) = (m - p < n).
Proof. by move=> ??; rewrite !ltn_subLR // addnC. Qed.

Lemma leq_ltn_subCl m n p : n <= m -> p <= m -> (m - n < p) = (m - p < n).
Proof. by move=> ??; rewrite !leq_ltn_subLR // addnC. Qed.

Lemma ltn_subCr m n p : (p < m - n) = (n < m - p).
Proof. by rewrite !ltn_subRL // addnC. Qed.

Lemma leq_subCr m n p : 0 < p -> 0 < n -> (p <= m - n) = (n <= m - p).
Proof. by move=> ??; rewrite !leq_subRL // addnC. Qed.

Lemma leq_leq_subCr m n p : n <= m -> p <= m -> (p <= m - n) = (n <= m - p).
Proof. by move=> ??; rewrite !leq_leq_subRL // addnC. Qed.

Lemma leq_subCl m n p : (m - n <= p) = (m - p <= n).
Proof. by rewrite !leq_subLR // addnC. Qed.

End MoreNatTheory.

Section MoreBigop.

Lemma big_morph_in (R1 R2 : Type)
  (f : R2 -> R1) (id1 : R1) (op1 : R1 -> R1 -> R1)
  (id2 : R2) (op2 : R2 -> R2 -> R2) (D : pred R2) :
  (forall x y, x \in D -> y \in D -> op2 x y \in D) ->
  id2 \in D ->
  {in D &, {morph f : x y / op2 x y >-> op1 x y}} ->
  f id2 = id1 ->
  forall  (I : Type) (r : seq I) (P : pred I) (F : I -> R2),
  all D [seq F x | x <- r & P x] ->
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof.
move=> Dop2 Did2 f_morph f_id I r P F.
elim: r => [|x r ihr /= DrP]; rewrite ?(big_nil, big_cons) //.
set b2 := \big[_/_]_(_ <- _ | _) _; set b1 := \big[_/_]_(_ <- _ | _) _.
have fb2 : f b2 = b1 by rewrite ihr; move: (P x) DrP => [/andP[]|].
case: (boolP (P x)) DrP => //= Px /andP[Dx allD].
rewrite f_morph ?fb2 // /b2 {b2 fb2 ihr b1 x Px Dx f_morph f_id}.
elim: r allD => [|x r ihr /=]; rewrite ?(big_nil, big_cons) //.
by case: (P x) => //= /andP [??]; rewrite Dop2 // ihr.
Qed.

Variables (R : Type) (idx : R).

Fact big_ord_exchange_cond {op : Monoid.law idx} {a b : nat}
   (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < a | P i && (i < b)) F i =
  \big[op/idx]_(i < b | P i && (i < a)) F i.
Proof.
wlog le_b_a : a b / b <= a => [hwlog|].
  have /orP [le_a_b|le_b_a] := leq_total a b; last exact: hwlog.
  by symmetry; apply: hwlog.
rewrite big_ord_narrow_cond /=; apply: eq_big => // i.
by rewrite (leq_trans _ le_b_a) ?andbT.
Qed.

Fact big_ord_exchange {op : Monoid.law idx} {a b : nat} (F : nat -> R) :
  \big[op/idx]_(i < a | i < b) F i =
  \big[op/idx]_(i < b | i < a) F i.
Proof. exact: (big_ord_exchange_cond xpredT). Qed.

Fact big_ord1 (op : Monoid.law idx) (F : nat -> R) :
  \big[op/idx]_(i < 1) F i = F 0.
Proof. by rewrite big_ord_recl big_ord0 Monoid.mulm1. Qed.

Lemma big_nat_widen_l (op : Monoid.law idx)
     (m1 m2 n : nat) (P : pred nat) (F : nat -> R) :
   m2 <= m1 ->
   \big[op/idx]_(m1 <= i < n | P i) F i =
   \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Proof.
move=> le_m2m1; have [ltn_m1n|geq_m1n] := ltnP m1 n; last first.
  rewrite big_geq // big_nat_cond big_pred0 // => i.
  by apply/negP => /and3P[/andP [_ /leq_trans]]; rewrite leqNgt => ->.
rewrite [RHS](@big_cat_nat _ _ _ m1) // 1?ltnW //.
rewrite [X in op X]big_nat_cond [X in op X]big_pred0; last first.
  by move=> i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
rewrite Monoid.mul1m [LHS]big_nat_cond [RHS]big_nat_cond.
by apply/eq_bigl => i; have [] := ltnP i m1; rewrite ?(andbT, andbF).
Qed.

Lemma big_mknat  (op : Monoid.law idx)  (a b : nat) (F : nat -> R) :
  \big[op/idx]_(i < b | a <= i) F i = \big[op/idx]_(a <= i < b) F i.
Proof.
rewrite -(big_mkord (fun i => a <= i) F).
by rewrite -(big_nat_widen_l _ _ predT) ?leq0n.
Qed.

End MoreBigop.

Section MoreCoef.

Open Scope ring_scope.

Lemma coefMD_wid (R : ringType) (p q : {poly R}) (m n i : nat) :
  i < m -> i < n ->
  (p * q)`_i = \sum_(j1 < m) \sum_(j2 < n | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
move=> m_big n_big; rewrite pair_big_dep.
pose tom := widen_ord m_big; pose ton := widen_ord n_big.
rewrite (reindex (fun j : 'I_i.+1 => (tom j, ton (rev_ord j)))) /=.
  rewrite coefM; apply: eq_big => //= j.
  by rewrite -maxnE (maxn_idPr _) ?eqxx ?leq_ord.
exists (fun k : 'I__ * 'I__ => insubd ord0 k.1) => /=.
  by move=> j _; apply/val_inj; rewrite val_insubd ltn_ord.
move=> [k1 k2] /=; rewrite inE /= {}/ton eq_sym => /eqP i_def.
apply/eqP; rewrite xpair_eqE -!val_eqE /= ?val_insubd i_def !ltnS.
by rewrite leq_addr eqxx /= subSS addKn.
Qed.

Lemma coefMD (R : ringType) (p q : {poly R}) (i : nat) :
 (p * q)`_i = \sum_(j1 < size p)
              \sum_(j2 < size q | (j1 + j2)%N == i) p`_j1 * q`_j2.
Proof.
rewrite (@coefMD_wid _ _ _ i.+1 i.+1) //=.
rewrite (bigID (fun j1 :'I__ => j1 < size p)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j1; rewrite -ltnNge => j1_big.
  by rewrite big1 // => j2 _; rewrite nth_default ?mul0r.
rewrite (big_ord_exchange
 (fun j1 => \sum_(j2 < i.+1 | (j1 + j2)%N == i) p`_j1 * q`_j2)) /=.
rewrite big_mkcond /=; apply: eq_bigr => j1 _; rewrite ltnS.
have [j1_small|j1_big] := leqP; last first.
  rewrite big1 // => j2; rewrite eq_sym => /eqP i_def.
  by rewrite i_def -ltn_subRL subnn ltn0 in j1_big.
rewrite (bigID (fun j2 :'I__ => j2 < size q)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  move=> j2; rewrite -ltnNge => /andP[_ j2_big].
  by rewrite [q`__]nth_default ?mulr0.
rewrite (big_ord_exchange_cond
 (fun j2 => (j1 + j2)%N == i) (fun j2 => p`_j1 * q`_j2)) /=.
rewrite big_mkcondr /=; apply: eq_bigr => k; rewrite ltnS.
have [//|j2_big] := leqP; rewrite eq_sym=> /eqP i_def.
by rewrite i_def addnC -ltn_subRL subnn ltn0 in j2_big.
Qed.

End MoreCoef.

Local Open Scope ring_scope.

Section MoreComUnitRingTheory.
Variable (R : comUnitRingType).

Lemma eq_divr (a b c d : R) : b \is a GRing.unit -> d \is a GRing.unit ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> b_unit d_unit; pose canM := (can2_eq (mulrVK _) (mulrK _)).
by rewrite canM // mulrAC -canM ?unitrV ?invrK.
Qed.

Lemma mulr_div (x1 y1 x2 y2 : R) :
  (y1 \is a GRing.unit) ->
  (y2 \is a GRing.unit) -> x1 / y1 * (x2 / y2) = x1 * x2 / (y1 * y2).
Proof. by move=> y1_unit y2_unit; rewrite mulrACA -invrM ?[y2 * _]mulrC. Qed.

Lemma addr_div (x1 y1 x2 y2 : R) :
  y1 \is a GRing.unit -> y2 \is a GRing.unit ->
  x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof.
move => y1_unit y2_unit.
by rewrite mulrDl [X in (_ * y1) / X]mulrC -!mulr_div ?divrr // !mulr1.
Qed.

End MoreComUnitRingTheory.

Section MoreFieldTheory.

Variable (K : fieldType).

Lemma eq_divf (a b c d : K) : b != 0 -> d != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof. by move=> b_neq0 d_neq0; rewrite eq_divr ?unitfE. Qed.

Lemma eq_divfC (a b c d : K) : a != 0 -> c != 0 ->
  (a / b == c / d) = (a * d == c * b).
Proof.
move=> ??; rewrite -invf_div -[c / d]invf_div (inj_eq (can_inj (@invrK _))).
by rewrite eq_divf // eq_sym [a * d]mulrC [b * c]mulrC.
Qed.

Lemma eq_divf_mul (a b c d : K) : a / b != 0 -> a / b = c / d -> a * d = c * b.
Proof.
have [->| d_neq0 ab0 /eqP] := eqVneq d 0.
  by rewrite !invr0 !mulr0 => /negPf ab0 /eqP; rewrite ab0.
rewrite eq_divf //; first by move/eqP.
by apply: contraNneq ab0 => ->; rewrite invr0 mulr0.
Qed.

End MoreFieldTheory.

Local Notation "p ^ f" := (map_poly f p).

Section AuxiliaryResults.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma perm_eq_nil (T : eqType) (s : seq T) : (s =p [::]) = (s == [::]).
Proof.
apply/idP/idP ; last by move/eqP ->.
move => H ; apply/eqP.
by apply: perm_small_eq.
Qed.

Fact head_rev (T : Type) (s : seq T) (x : T) : head x (rev s) = last x s.
Proof. by case/lastP: s => [//= |t y]; rewrite rev_rcons last_rcons //=. Qed.

Fact last_rev (T : Type) (s : seq T) (x : T) : last x (rev s) = head x s.
Proof. case: s => [//= |t y /=]; rewrite rev_cons last_rcons //=. Qed.

Lemma nseqS T (n : nat) (x : T) : nseq n.+1 x = rcons (nseq n x) x.
Proof. by elim: n => //= n <-. Qed.

Lemma rev_nseq T (n : nat) (x : T) : rev (nseq n x) = nseq n x.
Proof. by elim: n => // n; rewrite {1}nseqS rev_rcons => ->. Qed.

Lemma rev_ncons (T : Type) (n : nat) (x : T) (s : seq T) :
  rev (ncons n x s) = rev s ++ nseq n x.
Proof. by rewrite -cat_nseq rev_cat rev_nseq. Qed.

Lemma rem_cons  (T : eqType) (s : seq T) (a : T) : rem a (a :: s) = s.
Proof. by rewrite /= eqxx. Qed.

Lemma rcons_nil (T : eqType) (a : T) : rcons [::] a = [:: a].
Proof. by rewrite -cats1 cat0s. Qed.

Variable (R : ringType).
Implicit Types (p : {poly R}).

Lemma map_poly_mul (c : R) p : p ^ ( *%R c) = c *: p.
Proof. by apply/polyP => i; rewrite coefZ coef_map_id0 ?mulr0. Qed.

Lemma lead_coefMXn p (n : nat) : lead_coef (p * 'X^n) = lead_coef p.
Proof. by rewrite lead_coef_Mmonic ?monicXn //. Qed.

Lemma size_polyMXn p (n : nat) : p != 0 -> size (p * 'X^n) = (size p + n)%N.
Proof. by move=> ?; rewrite size_Mmonic ?monicXn // size_polyXn addnS. Qed.

Lemma widen_poly (E : nat -> R) (a b : nat) : a <= b ->
  (forall j, a <= j < b -> E j = 0) ->
  \poly_(i < a) E i = \poly_(i < b) E i.
Proof.
move=> leq_a_b E_eq0; apply/polyP => k; rewrite !coef_poly.
have [lt_ka|le_ak] := ltnP k a; first by rewrite (leq_trans lt_ka).
by have [lt_kb|//] := ifPn; rewrite E_eq0 // le_ak lt_kb.
Qed.

Lemma deriv_sum (T : Type) (s : seq T) (F : T -> {poly R}) (P : pred T):
  deriv (\sum_(i <- s | P i) F i) = \sum_(i <- s | P i) deriv (F i).
Proof. by apply: big_morph; [exact: derivD|exact: deriv0]. Qed.

Lemma poly_rcons (s : seq R) : Poly (rcons s 0) = Poly s.
Proof.
elim: s => [|a l ihs].
+ rewrite rcons_nil; apply/val_inj => /=.
  by rewrite polyseq_cons nil_poly polyC0 eqxx.
+ rewrite rcons_cons; apply/val_inj => /=.
  by rewrite ihs.
Qed.

Lemma poly_cat_nseq (s : seq R) (n : nat) : Poly (s ++ (nseq n 0)) = Poly s.
Proof.
elim: n => [|n ihn] ; first by rewrite cats0.
by rewrite nseqS -rcons_cat poly_rcons ihn.
Qed.

Lemma coef0M (p q : {poly R}) : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed.

Variable (K : fieldType).

(* p : {poly K} can be generalize ? *)
Fact modp_sumn (I : Type) (r : seq I) (P : pred I)
               (F : I -> {poly K}) (p : {poly K}) :
               (\sum_(i <- r | P i) F i) %% p = \sum_(i <- r | P i) (F i %% p).
Proof. by rewrite (big_morph ((@modp _)^~ p) (modp_add _) (mod0p _) _). Qed.

Fact modp_mul2 (p q m : {poly K}): ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

End AuxiliaryResults.

Module InjMorphism.

Section ClassDef.

Variables (R S : ringType).

Record class_of (f : R -> S) : Type :=
  Class {base : rmorphism f; mixin : injective f}.
Local Coercion base : class_of >-> rmorphism.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : injective f) :=
  fun (bF : GRing.RMorphism.map phRS) fA & phant_id (GRing.RMorphism.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical additive := GRing.Additive.Pack phRS class.
Canonical rmorphism := GRing.RMorphism.Pack phRS class.

End ClassDef.

Module Exports.
Notation injmorphism f := (class_of f).
Coercion base : injmorphism >-> GRing.RMorphism.class_of.
Coercion mixin : injmorphism >-> injective.
Coercion apply : map >-> Funclass.
Notation InjMorphism fM := (pack fM id).
Notation "{ 'injmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'injmorphism'  fRS }") : ring_scope.
Notation "[ 'injmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'injmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'injmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'injmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion rmorphism : map >-> GRing.RMorphism.map.
Canonical rmorphism.
End Exports.

End InjMorphism.
Include InjMorphism.Exports.

Section InjectiveTheory.

Lemma raddf_inj (R S : zmodType) (f : {additive R -> S}) :
   (forall x, f x = 0 -> x = 0) -> injective f.
Proof.
move=> f_inj x y /eqP; rewrite -subr_eq0 -raddfB => /eqP /f_inj /eqP.
by rewrite subr_eq0 => /eqP.
Qed.

Variable (R S : ringType) (f : {injmorphism R -> S}).

Lemma rmorph_inj : injective f. Proof. by case: f => [? []]. Qed.

Lemma rmorph_eq (x y : R) : (f x == f y) = (x == y).
Proof. by rewrite (inj_eq (rmorph_inj)). Qed.

Lemma rmorph_eq0 (x : R) : (f x == 0) = (x == 0).
Proof. by rewrite -(rmorph0 f) (inj_eq (rmorph_inj)). Qed.

Definition map_poly_injective : injective (map_poly f).
Proof.
move=> p q /polyP eq_pq; apply/polyP=> i; have := eq_pq i.
by rewrite !coef_map => /rmorph_inj.
Qed.

Canonical map_poly_is_injective := InjMorphism map_poly_injective.

End InjectiveTheory.
#[export]
Hint Resolve rmorph_inj : core.

Canonical polyC_is_injective (R : ringType) := InjMorphism (@polyC_inj R).

Canonical comp_is_injmorphism (R S T : ringType)
  (f : {injmorphism R -> S}) (g : {injmorphism S -> T}) :=
  InjMorphism (inj_comp (@rmorph_inj _ _ g) (@rmorph_inj _ _ f)).

(* Hack to go around a bug in canonical structure resolution *)
Definition fmorph (F R : Type) (f : F -> R) := f.
Canonical fmorph_is_injmorphism (F : fieldType) (R : ringType)
  (f : {rmorphism F -> R}) :=
  InjMorphism (fmorph_inj f : injective (fmorph f)).
