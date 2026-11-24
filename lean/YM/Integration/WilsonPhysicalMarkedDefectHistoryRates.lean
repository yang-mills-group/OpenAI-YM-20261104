import YM.Integration.WilsonPhysicalMarkedDefectWindow
import YM.Push.CORRECTED_COLUMNS.Vacuum

/-! The cost of the actual full mixed history is booked at its upper birth.
One lower threshold converts it to the measured coupling of any earlier station;
there is no factor for the number of times that history has been reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect
open Set Filter Lattice RG Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 AllOrder AllOrder.Transit WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open scoped Topology Classical

variable {G : Gauge}

private theorem prior_ratio (R:Run G) (simple:G.Simple) {j b:ℕ} (hj:j≤b)
    {fine upper:ℝ} (old:fine∈Shoot.band R.alloy.B.a j) (late:upper∈Shoot.band R.alloy.B.a b) :
    Coat.gStep upper≤2*Coat.gStep fine := by
  have earlier := Push.Corrected.Last.band_le R.alloy.B.a simple hj
  have x : 0<fine := (half_pos (WardBin.hot R.alloy.B.a j)).trans_le old.1
  have y : 0<upper := (half_pos (WardBin.hot R.alloy.B.a b)).trans_le late.1
  have four : fine ≤ 4*upper := by linarith only [old.2,late.1,earlier]
  have root := Real.sqrt_le_sqrt four
  rw [Real.sqrt_mul (by norm_num : 0≤(4:ℝ))] at root
  norm_num at root
  simpa only [Coat.gStep,one_div,div_eq_mul_inv,one_mul] using
    (div_le_div_iff₀ (Real.sqrt_pos.mpr y) (Real.sqrt_pos.mpr x)).mpr
      (by simpa only [one_mul] using root : 1*Real.sqrt fine ≤ 2*Real.sqrt upper)

private theorem pay_prior (C r t:ℝ) (hC:0≤C) (ht:0≤t) (gap:t<r) :
    ∀ᶠ β:ℝ in atTop, ∀ y:ℝ, 0≤y → Coat.gStep β≤2*y → C*(Coat.gStep β)^r≤y^t := by
  have coeff : 0 ≤ (2:ℝ)^t*C := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC
  filter_upwards [restored_rate ((2:ℝ)^t*C) r t 0 coeff (by linarith)] with β bill
  intro y hy comp
  have bt := bill 1 (by simp)
  have hroot : 0≤Coat.gStep β := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cmp := Real.rpow_le_rpow hroot comp ht
  rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hy] at cmp
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos (by norm_num : 0<(2:ℝ)) t)).mp
  calc
    (2:ℝ)^t * (C * Coat.gStep β ^ r) = (2^t*C)*1*(Coat.gStep β)^r := by ring
    _ ≤ (Coat.gStep β)^t := bt
    _ ≤ 2^t*y^t := cmp

/-- One physical threshold before both regulators, all periods and all prior
stations. It pays the published `4 × regular` and the entire divided hard
term of the genuine `MixedResets.Payment.fixed`. -/
theorem history_rates (R:Run G) (simple:G.Simple) (p s:ℕ) (ε η δ:ℝ)
    (ht:0≤(p:ℝ)+1-δ) (loss:η<δ) (high:(p:ℝ)+1-δ<((2*s:ℕ):ℝ)) :
    ∀ᶠ b:ℕ in atTop, ∀ j:ℕ, j≤b → ∀ βB:ℝ, βB∈Shoot.band R.alloy.B.a b →
      ∀ βF:ℝ, βF∈Shoot.band R.alloy.B.a j →
        4*((2:ℝ)^((p:ℝ)+1-4*ε)*(Coat.gStep βB)^((p:ℝ)+1-η)) ≤ (Coat.gStep βF)^((p:ℝ)+1-δ) ∧
        (2*Coat.gStep βB)^(2*s) ≤ (Coat.gStep βF)^((p:ℝ)+1-δ) := by
  obtain ⟨B,hB⟩ := eventually_atTop.1 (pay_prior (4*(2:ℝ)^((p:ℝ)+1-4*ε)) ((p:ℝ)+1-η)
    ((p:ℝ)+1-δ) (by positivity) ht (by linarith))
  obtain ⟨K,hK⟩ := eventually_atTop.1 (pay_prior ((2:ℝ)^(2*s)) ((2*s:ℕ):ℝ)
    ((p:ℝ)+1-δ) (by positivity) ht high)
  filter_upwards [(Sycamore.too R simple).eventually_ge_atTop (2*max B K)] with b grown
  intro j hj βB upper βF fine
  have ratio := prior_ratio R simple hj fine upper
  have nonneg : 0≤Coat.gStep βF := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have first := hB βB (by linarith only [upper.1,grown,le_max_left B K]) _ nonneg ratio
  have second := hK βB (by linarith only [upper.1,grown,le_max_right B K]) _ nonneg ratio
  constructor
  · simpa only [mul_assoc] using first
  · simpa only [Real.rpow_natCast, mul_pow] using second

end YM.Integration.WilsonPhysicalMarkedDefect
