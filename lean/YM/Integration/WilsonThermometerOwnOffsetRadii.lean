import YM.Integration.WilsonThermometerOwnOffsetNectar
import YM.Integration.ActualRunAdjacentHatBeta
import YM.Integration.ActualRunRatioGrowth

/-! The actual multiplicative widths pay the engineering powers of the
displaced Wilson columns from a single polynomial reporting radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetRadii
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open scoped Classical Topology
variable {G : Gauge} (R : Run G)
local notation "A" => R.alloy.B.a
local notation "β" => R.alloy.B.a.clock.hatBeta

def span (k j : ℕ) := R.family.S.a k/R.family.S.a j
def radius (t k j : ℕ) := march (fun _ : Unit => (β k^t)⁻¹) (near A) k j ()

theorem span_pos (k j : ℕ) : 0<span R k j :=
  div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)

theorem span_next (k j : ℕ) : span R k (j+1) = span R k j*(R.family.S.block j).val := by
  unfold span;rw [R.family.S.a_step,div_div_eq_mul_div];ring

theorem radius_start (t k : ℕ) : radius R t k k = (β k^t)⁻¹ := by
  unfold radius;rw [marines k (near A) _ (by intro; exact inv_pos.mpr (pow_pos (WardBin.hot A k) _))]

theorem radius_next (t k j : ℕ) (hj:k≤j) :
    radius R t k (j+1)=(β (j+1))⁻¹*radius R t k j := by
  simp only [radius,march,if_pos hj,near,sap]

theorem radius_pos (t k j : ℕ) (hj:k≤j) : 0<radius R t k j := by
  induction j,hj using Nat.le_induction with
  | base=>rw [radius_start];exact inv_pos.mpr (pow_pos (WardBin.hot A _) _)
  | succ j hj ih=>rw [radius_next R t k j hj];exact mul_pos (inv_pos.mpr (WardBin.hot A _)) ih

theorem stage (simple:G.Simple) (e t : ℕ) :
    ∀ᶠ j : ℕ in atTop, (R.family.S.block j).val^e * (β (j+1))^t ≤ β (j+1) * β j^t := by
  have temp := (WardBin.bell A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ActualRunAdjacentHatBeta.three_halves R simple,
    R.alloy.B.a.fits.deep.eventually_ge_atTop (2*e),temp.eventually_ge_atTop (((2:ℝ)^t)^2)]
    with j next depth hot
  let L : ℝ := (R.family.S.block j).val
  let x := β j
  let z := β (j+1)
  have lx : (1:ℝ)≤L := by
    change (1:ℝ) ≤ ((R.family.S.block j).val:ℝ)
    exact_mod_cast (show (1:ℕ) ≤ (R.family.S.block j).val from (R.family.S.block j).property)
  have xp : 0<x := WardBin.hot A _
  have zp : 0<z := WardBin.hot A _
  have pieces : (L^e)^2 ≤ z := by
    rw [←pow_mul,mul_comm e 2]
    exact (pow_le_pow_right₀ lx (Nat.le_succ _)).trans (ActualRunRatioGrowth.ratio_power_le R simple j _ depth)
  have gro : (2:ℝ)^t * L^e ≤z := by
    change ((2:ℝ)^t)^2 ≤ z at hot
    nlinarith only [hot,pieces,sq_nonneg ((2:ℝ)^t-L^e)]
  have adj : z≤2*x := by change z ≤ (3/2)*x at next;linarith
  calc L^e*z^t ≤ L^e*(2*x)^t := by gcongr
       _ = ((2:ℝ)^t*L^e)*x^t := by rw [mul_pow];ring
       _ ≤ z*x^t := mul_le_mul_of_nonneg_right gro (pow_nonneg xp.le _)

theorem paid (simple : G.Simple) (e t : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j ≥ k, radius R t k j * (span R k j)^e * (β j)^t ≤ 1 := by
  obtain ⟨k₀,steps⟩ := eventually_atTop.mp (stage R simple e t)
  filter_upwards [eventually_ge_atTop k₀] with k later j hj
  induction j,hj using Nat.le_induction with
  | base=>
    rw [radius_start,show span R k k=1 from div_self (R.family.S.a_pos k).ne',
      one_pow,mul_one,inv_mul_cancel₀ (pow_pos (WardBin.hot A _) _).ne']
  | succ j hj ih=>
    have X := steps j (later.trans hj)
    have z := WardBin.hot A (j+1)
    have part : ((R.family.S.block j).val:ℝ)^e * (β (j+1))^t / β (j+1) ≤ β j^t := by
      apply (div_le_iff₀ z).mpr; simpa only [mul_comm (β j^t)] using X
    rw [radius_next R t k j hj,span_next,mul_pow]
    calc _ = (radius R t k j*(span R k j)^e) *
             (((R.family.S.block j).val:ℝ)^e * (β (j+1))^t / β (j+1)) := by ring
         _ ≤ (radius R t k j*(span R k j)^e)*β j^t :=
           mul_le_mul_of_nonneg_left part (mul_nonneg (radius_pos R t k j hj).le (pow_nonneg (span_pos R k j).le _))
         _ ≤ 1 := ih

end YM.Integration.WilsonThermometerOwnOffsetRadii
end
