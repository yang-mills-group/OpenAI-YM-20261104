import YM.Integration.WilsonAddressedSharpTrialUnits
import YM.Integration.WilsonReflectedMixedSharpPanel
import YM.Integration.WilsonAddressedOrientedTrialWallet

/-! The holding price for any proper subset of one original submitted roster.
The inverse tolerance is chosen from its total arity before the collar mesh. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedTrialResidualRoster
open Finset Function Lattice RG Wilson Source Labels Marker QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicPivotRoster (Slot weight coord salaryOf)
open WilsonOriginalPublicFigureWick (project)
open WilsonAddressedSharpTrialUnits (fixed)
open WilsonAddressedTrialPivotUnits (ceiling row)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedMixedSharpPanel (reserve)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonAddressedFiniteThermalInput (vector)
open WilsonAddressedOrientedTrialWallet (factor)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {I:Type}[Fintype I][DecidableEq I](d j:I→ℕ){f K N p target:ℕ}
    (before:∀i,j i≤f)(up:f≤K)(live:K≤N){ζ:ℝ}(gain:0<ζ)
    (A:∀i,R.family.label (d i) ≃ₗ[ℂ] R.family.label (d i))
    (Y:∀i,R.family.label (d i))(amount:I→ℝ)
local notation "η" => reserve (Fintype.card I) ζ
variable (cash:∀i,Cash (R:=R) (d i) (j i) f K N p target (before i) up live (WilsonReflectedMixedSharpPanel.reserve (Fintype.card I) ζ) (A i) (Y i) (amount i))
    (arm:∀i,Arm R (d i) N p f K)(same:∀i,(arm i).w=(A i).symm (fitted R (d i) (j i) N p (Y i)))
    (c:I→ℝ)(x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I)))
local notation "a" => R.family.S.a
local notation "δ" => a K/a f
local notation "t_" => fun i=>(x i).val*(c i:ℂ)
local notation "v_" => fun i=>coords R (arm i)
local notation "net" => fun i=>fixed R W (d i) (j i) f η (t_ i) (amount i)
local notation "rent" => fun i=>ceiling R W (d i) f (t_ i) (v_ i)

theorem submitted (s:(Stock.census I).Mode)(i:s.val):
    vector R d N p K v_ (factor R d (K:=K) c) x s i=row R (d i.val) K N p (t_ i.val) (v_ i.val):=by
  simp only [vector,WilsonAddressedFiniteGuardTrial.submitted,factor,row,mul_assoc]

omit [Fintype I] [DecidableEq I] in
private theorem rent_nonneg (i:I):0≤rent i:=by
  have af:0≤a f:=(R.family.S.a_pos f).le
  have app:(0:ℝ)≤WilsonOriginalPublicPivotRoster.salaryOf W (R.family.labels.level (d i)):=
    Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have nn:0≤(R.family.labels.level (d i)).coeffSize (v_ i):=
    Finset.sum_nonneg fun _ _=>norm_nonneg _
  unfold ceiling
  positivity

omit [DecidableEq I] in
include cash same in
theorem income (s:Finset I):
    (∏i∈s,rent i) ≤ (∏i∈s,net i)*(a f/a K)^(η*(s.card:ℝ)):=by
  have point (i:I):rent i≤net i*(a f/a K)^η:=
    WilsonAddressedSharpTrialUnits.billed R W (before i) up live (A i) (Y i) (cash i) (arm i) (same i) (t_ i)
  refine (Finset.prod_le_prod (fun i _=>rent_nonneg R W d arm c x i) (fun i _=>point i)).trans_eq ?_
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_natCast,←Real.rpow_mul (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)).le]

omit [DecidableEq I] in
include gain cash same in
theorem paid (s:Finset I)(narrow:δ≤1):
    δ^ζ*(∏i∈s,rent i) ≤ δ^(3*ζ/4)*(∏i∈s,net i):=by
  have pos:=div_pos (R.family.S.a_pos K) (R.family.S.a_pos f)
  obtain ⟨ep,_,limit⟩:=WilsonReflectedMixedSharpPanel.margin (Fintype.card I) gain
  have count:(s.card:ℝ)≤Fintype.card I:=by exact_mod_cast s.card_le_univ
  have power:3*ζ/4≤ζ-η*(s.card:ℝ):=by
    nlinarith only [limit,mul_le_mul_of_nonneg_right count ep.le]
  have nn (i:I):0≤net i:=by
    have real:=rent_nonneg R W d arm c x i
    have turn:=real.trans (WilsonAddressedSharpTrialUnits.billed R W (before i) up live (A i) (Y i)
      (cash i) (arm i) (same i) (t_ i))
    exact nonneg_of_mul_nonneg_left turn (Real.rpow_pos_of_pos (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)) η)
  calc
    _ ≤ δ^ζ*((∏i∈s,net i)*(a f/a K)^(η*(s.card:ℝ))):=
      mul_le_mul_of_nonneg_left (income R W d j before up live A Y amount cash arm same c x s) (Real.rpow_nonneg pos.le _)
    _ = δ^(ζ-η*(s.card:ℝ))*(∏i∈s,net i):=by
      have flip:a f/a K=(a K/a f)⁻¹:=(inv_div ..).symm
      rw [flip,Real.inv_rpow pos.le,Real.rpow_sub pos]
      ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge pos narrow power)
      (Finset.prod_nonneg fun i _=>nn i)

end YM.Integration.WilsonAddressedTrialResidualRoster
end
