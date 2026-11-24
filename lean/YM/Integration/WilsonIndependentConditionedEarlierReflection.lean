import YM.Integration.WilsonAddressedPublicOpticalClock
import YM.Integration.WilsonIndependentConditionedEarlierThermal

/-! The amplitudes of a fixed power of a genuine earlier reflected width on the original clock. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedEarlierReflection
open Function Filter Set Finset Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open PhysicalNext.Repeat.Legato Lattice Wilson RG Source Extraction Next.Rank
open Next.Rank.Station Trace.Terrace WilsonReflectedOriginalPrefixTariff WilsonInvariantActionPosition
open MergeProof.East Next.UVStress WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonCoeffUV.Bank
open WilsonIndependentConditionedActualCredit (badge)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "M" => R.family.path.levels.clock.monitor

theorem monitor (simple:G.Simple)(nPow:ℕ){η:ℝ}(ep:0<η):∃B:ℝ,1≤B ∧ ∀{j i:ℕ},i≤j → (M i)^nPow≤B*((β j)^η):=by
  have deep:∀ᶠ i:ℕ in atTop,(M i)^nPow ≤ (β i)^η:=by
    filter_upwards [(hat_rate (A) simple).eventually (Vac.Numbers.cost (nPow:ℝ) η ep)] with i bound
    simpa [Vac.Numbers.P,Calendar.monitor,Real.rpow_natCast] using bound
  have monotone:=WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le
  obtain ⟨n,late⟩:=eventually_atTop.mp deep
  let B:=1+∑i∈range n,(M i)^nPow
  have nn:0 ≤ ∑i∈range n,(M i)^nPow:=sum_nonneg (fun _ _=>pow_nonneg (Real.exp_pos _).le nPow)
  have one:1 ≤ B:=by dsimp only [B];linarith only [nn]
  refine ⟨B,one,?_⟩
  intro j i ij
  have bp:1 ≤ β j:=((A).fits.delayed j).le
  have pos:0 ≤ (β j)^η:=Real.rpow_nonneg (zero_le_one.trans bp) _
  by_cases mature : n ≤ i
  · exact (late i mature).trans ((Real.rpow_le_rpow (zero_le_one.trans ((A).fits.delayed i).le)
      (monotone ij) ep.le).trans (le_mul_of_one_le_left pos one))
  · have inside:i∈range n:=mem_range.mpr (Nat.lt_of_not_ge mature)
    have whole: (M i)^nPow ≤ ∑k∈range n,(M k)^nPow:=single_le_sum (f:=fun j=>(M j)^nPow) (fun j _=>pow_nonneg (Real.exp_pos _).le _) inside
    exact (whole.trans (by dsimp only [B];linarith : _ ≤ B)).trans
      (le_mul_of_one_le_right (zero_le_one.trans one) (Real.one_le_rpow bp ep.le))


theorem four (simple:G.Simple)(spatial width:ℕ)(constant:ℝ){η:ℝ}(ep:0<η):
    ∀ᶠ f:ℕ in atTop,∀j:ℕ,j≤f→∀v:ℝ,0≤v→v^spatial≤(β f)^(η/8) →
      constant*v^spatial*(M j)^width ≤ (thermal R f)^(-η):=by
  obtain ⟨B,_,pr⟩:=monitor R simple width (η:=η/8) (by positivity)
  let J:Credit:=⟨0,max 1 (|constant| *B),le_max_left ..⟩
  filter_upwards [WilsonIndependentConditionedActualCredit.subpower R simple J (half_pos ep)] with f paid
  intro j jf v pos enough
  have bp:0<β f:=zero_lt_one.trans ((A).fits.delayed f)
  have gp:0<thermal R f:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have fixed:|constant| *B≤(thermal R f)^(-(η/2)):=by
    have c:max 1 (|constant| *B) ≤ (thermal R f)^(-(η/2)):=by simpa only [Credit.buy,J,pow_zero,mul_one] using paid
    exact (le_max_right ..).trans c
  have ident:(β f)^(η/4)=(thermal R f)^(-(η/2)):=by
    change _=((Real.sqrt (β f))⁻¹)^(-(η/2))
    rw [Real.inv_rpow (Real.sqrt_nonneg _) _,Real.sqrt_eq_rpow,←Real.rpow_mul bp.le,←Real.rpow_neg bp.le]
    congr 1
    ring
  calc
    constant*v^spatial*(M j)^width ≤ |constant| *((β f)^(η/8))*(B*((β f)^(η/8))):=by
      apply mul_le_mul _ (pr jf) (pow_nonneg (Real.exp_pos _).le _) (by positivity)
      exact mul_le_mul (le_abs_self _) enough (pow_nonneg pos _) (abs_nonneg _)
    _ = (|constant| *B)*(β f)^(η/4):=by
      rw [show η/4=η/8+η/8 by ring,Real.rpow_add bp];ring
    _ ≤ (thermal R f)^(-(η/2))*(thermal R f)^(-(η/2)):=by
      rw [ident];exact mul_le_mul_of_nonneg_right fixed (Real.rpow_nonneg gp.le _)
    _ = (thermal R f)^(-η):=by rw [←Real.rpow_add gp];congr 1;ring

end YM.Integration.WilsonIndependentConditionedEarlierReflection
