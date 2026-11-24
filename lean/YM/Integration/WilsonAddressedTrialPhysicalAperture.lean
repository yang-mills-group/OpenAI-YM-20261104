import YM.Integration.WilsonAddressedTrialResidualRoster

/-! Use the stable gain on the genuinely compensated assessed arms of
the common face. Their home price is chosen before the planting depth. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonAddressedTrialPhysicalAperture
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


omit [DecidableEq I] in
include gain cash same in
theorem original (s:Finset I){g depth pole target H:ℝ}
    (gp:0<g)(small:g ≤ 1)(depth_nonneg:0 ≤ depth)(fund:0 ≤ H)
    (apart:δ ≤ g^depth)(budget:target+pole ≤ depth*(3*ζ/4))
    (homes:(∏i∈s,net i) ≤ H*g^(-pole)):
    δ^ζ*(∏i∈s,rent i) ≤ H*g^target:=by
  have step:0 ≤ δ:=(div_pos (R.family.S.a_pos K) (R.family.S.a_pos f)).le
  have narrow:=apart.trans (Real.rpow_le_one gp.le small depth_nonneg)
  have positive:0 ≤ 3*ζ/4:=by positivity
  calc
    _ ≤ δ^(3*ζ/4)*(∏i∈s,net i):=
      WilsonAddressedTrialResidualRoster.paid R W d j before up live gain A Y amount cash arm same c x s narrow
    _ ≤ δ^(3*ζ/4)*(H*g^(-pole)):=mul_le_mul_of_nonneg_left homes (Real.rpow_nonneg step _)
    _ ≤ (g^depth)^(3*ζ/4)*(H*g^(-pole)):=mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow step apart positive) (mul_nonneg fund (Real.rpow_nonneg gp.le _))
    _ = H*g^(depth*(3*ζ/4)+(-pole)):=by rw [←Real.rpow_mul gp.le,Real.rpow_add gp];ring
    _ ≤ H*g^target:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge gp small (by linarith)) fund
end YM.Integration.WilsonAddressedTrialPhysicalAperture
end
