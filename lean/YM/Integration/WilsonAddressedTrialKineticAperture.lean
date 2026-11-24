import YM.Integration.WilsonAddressedTrialPhysicalAperture
import YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh

/-! Use the stable gain on the genuinely compensated assessed arms of
the common face. Their home price is chosen before the planting depth. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonAddressedTrialKineticAperture
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


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)

theorem scale (t f:ℕ):
    a (berth R t f)/a f ≤ (thermal R f)^(2*t) := by
  let β:=R.family.path.levels.clock.hatBeta f
  have bp:0<β:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have paid:a (berth R t f)/a f ≤ 1/β^t:=(div_le_div_iff₀ (R.family.S.a_pos f) (pow_pos bp t)).mpr
    (by simpa only [one_mul] using (WilsonInvariantActionPosition.arrival R t f).2)
  change a (berth R t f)/a f ≤ ((Real.sqrt β)⁻¹)^(2*t)
  simpa only [pow_mul,inv_pow,Real.sq_sqrt bp.le,one_div] using paid

theorem reserve {wanted pole:ℝ} (gain:0<ζ):
    ∃ t:ℕ, ∀u:ℕ, t≤u → wanted+pole ≤ ((2*u:ℕ):ℝ)*(3*ζ/4) := by
  let hi:ℝ:=3*ζ/2
  have pos:0<hi:=by dsimp [hi];positivity
  obtain ⟨t,ht⟩:=exists_nat_ge ((wanted+pole)/hi)
  refine ⟨t,fun u hu=>?_⟩
  have shift:((t:ℕ):ℝ)≤(u:ℝ):=by exact_mod_cast hu
  have cover:=(div_le_iff₀ pos).mp (ht.trans shift)
  push_cast
  dsimp [hi] at cover
  linarith

omit [DecidableEq I] in
include gain cash same in
theorem original (s:Finset I)(t:ℕ)(chosen:K=berth R t f)
    {pole target H:ℝ}(fund:0≤H)(budget:target+pole≤((2*t:ℕ):ℝ)*(3*ζ/4))
    (homes:(∏i∈s,net i) ≤ H*(thermal R f)^(-pole)):
    δ^ζ*(∏i∈s,rent i) ≤ H*(thermal R f)^target:=by
  let β:=R.family.path.levels.clock.hatBeta f
  have b1:1≤β:=(R.family.path.levels.fits.delayed f).le
  have bp:0<β:=zero_lt_one.trans_le b1
  have gs:thermal R f≤1:=by
    apply inv_le_one_of_one_le₀
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt b1
  apply WilsonAddressedTrialPhysicalAperture.original R W d j before up live gain A Y amount cash arm same c x s
    (inv_pos.mpr (Real.sqrt_pos.mpr bp)) gs (Nat.cast_nonneg (2*t)) fund _ budget homes
  rw [chosen,Real.rpow_natCast]
  exact scale R t f
end YM.Integration.WilsonAddressedTrialKineticAperture
end
