import YM.Integration.WilsonPhysicalExteriorMeshStops
import YM.RG16.GaugeCredit.Lambda

/-! Control the birth coupling of an actual marked Wilson insertion throughout
the first physical ultraviolet window, including for two independently chosen
cutoffs and periods. The quotient occurs before taking the field degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryBirthClock

open Filter Real Lattice Wilson RG RG16 RG16.Literal Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops
open scoped Topology

variable {G : Gauge}

private theorem paid (C : Family G) (hG : G.Simple) (c : ℝ) :
    ∀ᶠ k : ℕ in atTop, 2*G.slopeConstant*(Lambda C.path.levels k)^c ≤ C.path.levels.clock.hatBeta k := by
  have small := ((isLittleO_rpow_exp_atTop c).const_mul_left (2*G.slopeConstant)).bound (Real.exp_pos (-2))
  filter_upwards [(lambda_leads C hG).eventually small] with k h
  have debit : |2*G.slopeConstant*(Lambda C.path.levels k)^c| ≤
      exp (-2)*|exp (Lambda C.path.levels k)| := by simpa only [Real.norm_eq_abs] using h
  have pos := zero_lt_one.trans (C.path.levels.fits.delayed k)
  rw [abs_of_pos (exp_pos _), ←exp_add,show -2+Lambda C.path.levels k=log (C.path.levels.clock.hatBeta k) by unfold Lambda; ring,
    exp_log pos] at debit
  exact (le_abs_self _).trans debit

/-- The first crossing, including its overshoot, keeps the monitored
    temperature comparable for every ordered or unordered pair of stages. -/
theorem temperatures (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : 1 ≤ c) :
    ∀ᶠ k : ℕ in atTop, ∀ {i j : ℕ}, k ≤ i → j ≤ ultraviolet R.family c k →
      R.family.path.levels.clock.hatBeta j ≤ 2 * R.family.path.levels.clock.hatBeta i := by
  let C := R.family
  let β := C.path.levels.clock.hatBeta
  let Λ := Lambda C.path.levels
  let u := ultraviolet C c
  have mono : Monotone β := fun i j ij => by
    change _+G.slopeConstant*C.S.scale i ≤ _+G.slopeConstant*C.S.scale j
    linarith only [mul_le_mul_of_nonneg_left ((OPE.scale_mono C.S).monotone ij) (Gauge.slopeConstant_pos hG).le]
  filter_upwards [ultraviolet_window C hG slow.2 c,paid C hG c] with k window fund
  have hk : 1 < Λ k := lt_trans (by norm_num : (1:ℝ)<2) (lambda_up C k)
  have z : 1 < Λ k + log 2 := by linarith only [hk,Real.log_pos (by norm_num : (1:ℝ)<2)]
  have l2 : log (2:ℝ) ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have extra : log (log (Λ k + log 2)) ≤ Λ k := by
    linarith only [log_le_sub_one_of_pos (log_pos z),log_le_sub_one_of_pos (by linarith only [z] : 0<Λ k+log 2),l2]
  have linear : Λ k ≤ (Λ k)^c := by simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hk.le hc
  have span : C.S.scale (u k) - C.S.scale k ≤ 2*(Λ k)^c := by
    have hi : C.S.scale (u k) - C.S.scale k ≤ (Λ k)^c + log (log (Λ k+log 2)) := window.2.2
    linarith only [hi,extra,linear]
  have diff : β (u k)-β k = G.slopeConstant*(C.S.scale (u k)-C.S.scale k) := by
    change (_+_*(C.S.scale (u k))) - (_+_*(C.S.scale k)) = _
    ring
  have top : β (u k) ≤ 2*β k := by
    change 2*G.slopeConstant*(Λ k)^c ≤ β k at fund
    linarith only [diff,mul_le_mul_of_nonneg_left span (Gauge.slopeConstant_pos hG).le,fund]
  intro i j ki ju
  exact (mono ju).trans (top.trans (mul_le_mul_of_nonneg_left (mono ki) (by norm_num)))

/-- The native field's engineering grade costs at most a fixed factor even
    if its birth coupling is carried intact from a different physical level. -/
theorem graded (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : 1 ≤ c) :
    ∀ᶠ k : ℕ in atTop, ∀ {i j : ℕ}, k ≤ i → j ≤ ultraviolet R.family c k →
      ∀ N n M m, i ≤ N → j ≤ M → ∀ h : ℕ,
        (regulatorRun R.family N n i / regulatorRun R.family M m j)^h ≤ (4:ℝ)^h := by
  filter_upwards [temperatures R hG slow hc] with k wrap
  intro i j ki ju N n M m iN jM h
  let C := R.family
  let x := C.path.β N n i
  let y := C.path.β M m j
  have xi : 0 < x := Overlay.beta_positive R.makes.wilson iN
  have yj : 0 < y := Overlay.beta_positive R.makes.wilson jM
  have dx := (R.makes.wilson.represents N n i iN).band.1
  have dy := (R.makes.wilson.represents M m j jM).band.2
  have hx : R.family.path.levels.clock.hatBeta i / 2 ≤ x := dx
  have hy : y ≤ 2*R.family.path.levels.clock.hatBeta j := dy
  have yy : y ≤ 16*x := by linarith only [hx,hy,wrap ki ju,xi]
  have sq : Real.sqrt y ≤ 4*Real.sqrt x := by
    simpa only [Real.sqrt_mul (by norm_num : (0:ℝ)≤16),show Real.sqrt 16 = (4:ℝ) by norm_num] using Real.sqrt_le_sqrt yy
  have sx := Real.sqrt_pos.mpr xi
  have sy := Real.sqrt_pos.mpr yj
  have quotient : regulatorRun C N n i / regulatorRun C M m j ≤ 4 := by
    change (Real.sqrt x)⁻¹ / (Real.sqrt y)⁻¹ ≤ 4
    rw [div_inv_eq_mul,inv_mul_eq_div,div_le_iff₀ sx]
    exact sq
  exact pow_le_pow_left₀ (div_nonneg (g_pos R.makes iN).le (g_pos R.makes jM).le) quotient _

end YM.Integration.WilsonPhysicalHistoryBirthClock

