From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import order.

Require Import auxresults natbar directed tfps invlim fps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fps_scope.


Reserved Notation "{ 'flps' R }"
         (at level 0, R at level 2, format "{ 'flps'  R }").

Definition laurent_series (R : idomainType) := {fraction {fps R}}.
Notation "{ 'flps' R }" := (laurent_series R).

Section Laurent.

Variable (R : fieldType).
Implicit Type (x y : {flps R}) (f g : {fps R}).


Lemma flps_uniqueP x :
  exists! (n : nat) (f : {fps R}),
    ((n == 0%N) || (f \is a GRing.unit)) /\ x = pi {flps R} (Ratio f (''X ^+ n)).
Proof.
elim/quotW: x => [[[num den]/= den_eq0]].
have/fpsf_XnfE:= den_eq0 => [][vd][sd][sdunit nd]; subst den.
(* have sd_neq0 : sd != 0.
  by move: den_eq0; rewrite mulf_eq0 negb_or expf_neq0 ?fpsX_eq0.
 *)
case: (valuatXnP num) => [vn sn sunit|] ->{num}; first last.
  exists 0%N; split; first last.
    case=> [|n'][f']//= [][]/= f'_unit + _.
    move/eqP; rewrite piE equivfE eq_sym.
    rewrite !(numer_Ratio, denom_Ratio, expf_neq0, fpsX_eq0) //=.
    rewrite mul0r mulf_eq0 (negbTE den_eq0) /= => /eqP f'0.
    by move: f'_unit; rewrite f'0 unitr0.
  exists 0; split => [|f']; first last.
    move=> [_ /eqP]; rewrite piE equivfE => /eqP /=.
    rewrite mul0r expr0 numer_Ratio ?oner_eq0 // => /esym/eqP.
    by rewrite mulf_eq0 (negbTE den_eq0) /= => /eqP ->.
  split; first by rewrite eqxx.
  apply/eqP; rewrite piE equivfE.
  by rewrite !(numer_Ratio, denom_Ratio, expr0, oner_eq0) //= mulr0 mul0r.
exists (vd - vn)%N; split; first last.
  case=> [|n'][f']//= [][].
    move=> _ /eqP; rewrite piE equivfE /= expr0 /=.
    rewrite !(numer_Ratio, denom_Ratio, oner_eq0) //=.
    rewrite mulr1 eq_sym => /eqP eqf _.
    apply/eqP; rewrite subn_eq0.
    move: eqf => /esym/(congr1 (fun f => f``_vn))/eqP.
    rewrite -mulrA !coef_fpsXnM ltnn subnn ltnNge.
    by case: leqP => //= _; rewrite (negbTE sunit).
  move=> f'unit /eqP; rewrite piE equivfE /=.
  rewrite !(numer_Ratio, denom_Ratio, expf_neq0, fpsX_eq0) //= => /eqP + _.
  rewrite mulrC mulrA -exprD -mulrA => /(congr1 (valuat (ilT := {fps R}))).
  rewrite !valuatXnE //; last by rewrite -fpsf_unitE unitrM f'unit sdunit.
  by move=> [<-]; rewrite addnK.
exists (''X ^+ (vn - vd)%N * sn / sd); split; first last.
  rewrite subn_eq0 => f' [f'unit /eqP].
  rewrite piE equivfE /= !(numer_Ratio, denom_Ratio, expf_neq0, fpsX_eq0) //=.
  rewrite mulrC mulrA -exprD; move: f'unit.
  case: ltnP => [/ltnW levnd /= f'unit | levdn _].
    rewrite subnK // => /eqP.
    move: levnd; rewrite -subn_eq0 => /eqP ->; rewrite expr0 mul1r.
    rewrite -!mulrA => /lreg_fpsXn ->.
    by rewrite [sd * f']mulrC mulrK.
  have:= levdn; rewrite -subn_eq0 => /eqP ->; rewrite add0n => /eqP H.
  have: GRing.lreg sd.
    by apply/lregP; move: den_eq0; rewrite mulf_eq0 negb_or expf_neq0 ?fpsX_eq0.
  apply; rewrite mulrC divrK //.
  by apply: (@lreg_fpsXn _ vd); rewrite !mulrA -exprD subnKC.
rewrite subn_eq0; case: ltnP => /= [/ltnW ltvnd | levdn].
  have:= ltvnd; rewrite -subn_eq0 => /eqP ->; rewrite expr0 mul1r.
  split; first by rewrite unitrM unitrV sdunit fpsf_unitE sunit.
  apply/eqP; rewrite piE equivfE; apply/eqP.
  rewrite !(numer_Ratio, denom_Ratio, expf_neq0, fpsX_eq0) //=.
  by rewrite [LHS]mulrC mulrA -exprD subnK // -mulrA [sd * _]mulrC divrK.
split=> //; apply/eqP; rewrite piE equivfE /=; apply/eqP.
rewrite !(numer_Ratio, denom_Ratio, expf_neq0, fpsX_eq0) //=.
have:= levdn; rewrite -subn_eq0 => /eqP ->; rewrite expr0 mulr1.
rewrite !mulrA [_ * ''X ^+ _]mulrC !mulrA -exprD subnK //.
by rewrite -!mulrA [sd * _]mulrC divrK.
Qed.

End Laurent.

