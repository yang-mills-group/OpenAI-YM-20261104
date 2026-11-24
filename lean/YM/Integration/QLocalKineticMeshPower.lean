import YM.Integration.ActualRunAdjacentHatBeta
import YM.IterationFour.Kinetic

/-! The actual kinetic mesh, purchased before the independent cutoff and physical
period, buys any requested coupling grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalKineticMeshPower

open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato IterationFour Pert.Asymptotics
open scoped Topology
variable {G:Gauge} (R:Run G) (hG:G.Simple)
include hG

/-- This price concerns only the original physical inverse couplings. It is
independent of every fitted kinetic predictor or marked formal catalogue. -/
theorem physicalInverse : ∀ᶠ m:ℕ in atTop,∀ N period:ℕ,m<N →
    (R.family.path.β N period m)⁻¹≤6*(regulatorRun R.family N period (m+1))^2 := by
  filter_upwards [ActualRunAdjacentHatBeta.three_halves R hG] with m adj N period hm
  change R.family.path.levels.clock.hatBeta (m+1) ≤ (3/2:ℝ)*R.family.path.levels.clock.hatBeta m at adj
  let c:=R.family.path.β N period m
  let f:=R.family.path.β N period (m+1)
  have hc:0<c:=Overlay.beta_positive R.makes.wilson hm.le
  have hf:0<f:=Overlay.beta_positive R.makes.wilson (Nat.succ_le_of_lt hm)
  have lo:R.family.path.levels.clock.hatBeta m/2≤c:=
    (R.makes.wilson.represents N period m hm.le).band.1
  have up:f≤2*R.family.path.levels.clock.hatBeta (m+1):=
    (R.makes.wilson.represents N period (m+1) (Nat.succ_le_of_lt hm)).band.2
  change c⁻¹≤6*((Real.sqrt f)⁻¹)^2
  rw [inv_pow,Real.sq_sqrt hf.le,←div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ hc hf).mpr
  linarith only [lo,up,adj]

theorem mesh (q:ℕ) : ∀ᶠ m:ℕ in atTop,∀ N period:ℕ,m<N →
    let g:=regulatorRun R.family N period (m+1)
    (Kinetic.price R.family m^q)⁻¹*g^2≤(3/2:ℝ)^q*g^(2*q+2) := by
  filter_upwards [ActualRunAdjacentHatBeta.three_halves R hG] with m adj N period hm
  change R.family.path.levels.clock.hatBeta (m+1) ≤ (3/2:ℝ)*R.family.path.levels.clock.hatBeta m at adj
  let β:=R.family.path.β N period (m+1)
  let g:=regulatorRun R.family N period (m+1)
  let b:=Kinetic.price R.family m
  have hb:0<b:=Kinetic.price_pos _ _
  have hf:0<β:=Overlay.beta_positive R.makes.wilson (Nat.succ_le_of_lt hm)
  have bf:β≤2*R.family.path.levels.clock.hatBeta (m+1):=
    (R.makes.wilson.represents N period (m+1) (Nat.succ_le_of_lt hm)).band.2
  have bh:2*R.family.path.levels.clock.hatBeta m≤b:=Kinetic.two_hat_le _ _
  have bf':β≤(3/2)*b:=by linarith only [bf,adj,bh]
  have eq:g^2=β⁻¹:=by change ((Real.sqrt β)⁻¹)^2=_; rw [inv_pow,Real.sq_sqrt hf.le]
  have buy:b⁻¹≤(3/2)*g^2:=by
    rw [eq,←div_eq_mul_inv,inv_eq_one_div]
    apply (div_le_div_iff₀ hb hf).mpr
    linarith only [bf']
  calc
    (b^q)⁻¹*g^2=(b⁻¹)^q*g^2:=by rw [inv_pow]
    _≤((3/2:ℝ)*g^2)^q*g^2:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hb.le) buy _) (sq_nonneg _)
    _=(3/2:ℝ)^q*g^(2*q+2):=by rw [mul_pow,←pow_mul,pow_add]; ring

theorem requested (p:ℕ) : ∀ᶠ m:ℕ in atTop,∀ N period:ℕ,m<N →
    let g:=regulatorRun R.family N period (m+1)
    (Kinetic.price R.family m^p)⁻¹*g^2≤(3/2:ℝ)^p*g^(p+1) := by
  filter_upwards [mesh R hG p,(tendsto_add_atTop_nat 1).eventually
    (Currency.g_small hG R.makes 1 zero_lt_one)] with m paid small N per hm
  exact (paid N per hm).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt hm)).le
      (small N per (Nat.succ_le_of_lt hm)).le (by omega)) (by positivity))

end YM.Integration.QLocalKineticMeshPower
