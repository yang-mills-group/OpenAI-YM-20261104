import YM.Integration.WilsonMovingKernelProfile

/-! The actual original positive Wilson profile in coordinates of the
incoming physical scale. The endpoint is the measured bare coupling. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringLocalClock
open Function Filter Lattice RG Pert.Asymptotics PhysicalNext.Repeat.Legato
open PertExtension.Series.Tested
open scoped Topology

variable {G : Gauge} (R : Run G) (N p i : ℕ)

def clock (g : ℝ) : ℝ :=
  g / Real.sqrt (1+(R.family.beta N p-R.family.path.β N p i)*g^2)

local notation "gᵢ" => regulatorRun R.family N p i
local notation "gₙ" => regulatorRun R.family N p N

private theorem hot (hi : i≤N) :
    0<R.family.path.β N p i := by
  rw [← WilsonPhysicalKernelClock.temperature R N p i hi]
  exact inv_pos.mpr (sq_pos_of_pos (IterationFour.Currency.g_pos R.makes N p i hi))

theorem radicand (hi : i≤N) {g : ℝ} (hg : 0<g) (hle : g≤gᵢ) :
    0<1+(R.family.beta N p-R.family.path.β N p i)*g^2 := by
  have hI : 0<(gᵢ) := IterationFour.Currency.g_pos R.makes N p i hi
  have hn : 0<R.family.beta N p := hot R N p N le_rfl
  have hfull : R.family.path.β N p i*gᵢ^2 = 1 := by
    rw [← WilsonPhysicalKernelClock.temperature R N p i hi, inv_mul_cancel₀ (pow_ne_zero _ hI.ne')]
  have hsmall : R.family.path.β N p i*g^2 ≤ 1 := by
    rw [← hfull]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.le hle 2) (hot R N p i hi).le
  nlinarith only [hsmall,mul_pos hn (sq_pos_of_pos hg)]

theorem positive (hi : i≤N) {g : ℝ} (hg : 0<g) (hle : g≤gᵢ) :
    0<clock R N p i g :=
  div_pos hg (Real.sqrt_pos.mpr (radicand R N p i hi hg hle))

theorem temperature (hi : i≤N) {g : ℝ} (hg : 0<g) (hle : g≤gᵢ) :
    ((clock R N p i g)^2)⁻¹ = (g^2)⁻¹ + (R.family.beta N p-R.family.path.β N p i) := by
  rw [clock,div_pow,Real.sq_sqrt (radicand R N p i hi hg hle).le,inv_div]
  field_simp [hg.ne']

/-- The actual local Wilson kernel receives exactly the incoming inverse
temperature on the whole positive interval through the measured endpoint. -/
theorem profile (hi : i≤N) {g : ℝ} (hg : 0<g) (hle : g≤gᵢ) :
    WilsonMovingKernelProfile.value R N p (clock R N p i g) i = (g^2)⁻¹ := by
  rw [WilsonMovingKernelProfile.value,if_neg (positive R N p i hi hg hle).ne',
    temperature R N p i hi hg hle]
  ring

theorem endpoint (hi : i≤N) : clock R N p i gᵢ = gₙ := by
  have hI : 0<(gᵢ) := IterationFour.Currency.g_pos R.makes N p i hi
  have hN : 0<(gₙ) := IterationFour.Currency.g_pos R.makes N p N le_rfl
  have hc : 0<clock R N p i (gᵢ) := positive R N p i hi hI le_rfl
  have htemp := temperature R N p i hi (g:=(gᵢ)) hI le_rfl
  have hsame : ((clock R N p i gᵢ)^2)⁻¹ = (gₙ^2)⁻¹ := by
    rw [htemp,WilsonPhysicalKernelClock.temperature R N p i hi,
      WilsonPhysicalKernelClock.temperature R N p N le_rfl]
    change _=R.family.beta N p
    ring
  have hh := congrArg Real.sqrt (inv_injective hsame)
  simpa only [Real.sqrt_sq hc.le,Real.sqrt_sq hN.le] using hh

theorem first (g : ℝ) : clock R N p N g = g := by
  change g/Real.sqrt (1+(R.family.beta N p-R.family.beta N p)*g^2)=g
  simp

theorem germ (hi : i≤N) :
    ∀ᶠ g in PertExtension.Series.Tested.germ,
      0<clock R N p i g ∧ WilsonMovingKernelProfile.value R N p (clock R N p i g) i=(g^2)⁻¹ := by
  filter_upwards [eventually_small (t:=gᵢ) (IterationFour.Currency.g_pos R.makes N p i hi)]
    with g hg
  exact ⟨positive R N p i hi hg.1 hg.2.le,profile R N p i hi hg.1 hg.2.le⟩

end YM.Integration.WilsonLimitConstruction.FundedSpringLocalClock
