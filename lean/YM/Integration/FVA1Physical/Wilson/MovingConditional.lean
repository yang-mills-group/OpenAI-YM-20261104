import YM.Integration.FVA1Physical.Wilson.MovingTicket

/-! The same tag sum and the full physical vacuum occur in the conditional
ray reading. Both the auxiliary Gaussian and absolute vacuum cancel exactly,
coefficientwise, against the installed independent FVA2 prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Function PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots FormalOPE.RG10.MultiGauge
open FVA2 FVA2.CityHistory
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (Z : ChartRatio G) (u : Pins G c) (a : ℕ → ℝ)

def rayTotal (J : d.Tags → PathSource (G:=G) d) : ℝ → ℝ := ∑ t, rayReading d a t u (J t)
def rayBank (W : SpaceF G d → ℝ) : ℕ → ℝ := ∑ t, rayCoefficient d Z a t u W

private theorem bank_series (W : SpaceF G d → ℝ) :
    mk (rayBank d Z u a W) = ∑ t, mk (rayCoefficient d Z a t u W) := by
  apply PowerSeries.ext; intro j
  simp [rayBank,Finset.sum_apply]

private theorem vacuum_series (t : d.Tags) (hZ : LocalRatio Z) (h : d.Room G) :
    mk (rayCoefficient d Z a t u 1) = C (rayFactor d Z t u h) *
    Stack.read u (μLedger d Z t h (Delay.stones a)) := by
  rw [ray_ticket d Z t u (W:=1) contDiffAt_const hZ h a,
    share_part d t (Delay.stones a) h _ Z hZ, Stack.rise_one,mul_one]
  rfl

private theorem vacuum_lead (hZ : LocalRatio Z) (h : d.Room G) : 0 < rayBank d Z u a 1 0 := by
  simp only [rayBank,Finset.sum_apply]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro t _
  rw [← coeff_mk 0 (rayCoefficient d Z a t u 1),vacuum_series d Z u a t hZ h,coeff_C_mul,Stack.reading_term,
    coeff_zero_eq_constantCoeff_apply,marketZ d Z t h (Delay.stones a) hZ]
  exact mul_pos (rayFactor_pos d Z t u hZ h) one_pos

private theorem bank_factor (hZ : LocalRatio Z) (h : d.Room G) (t₀ : d.Tags)
    {W : SpaceF G d → ℝ} (hw : ContDiffAt ℝ ω W 0) :
    mk (rayBank d Z u a W) = mk (rayBank d Z u a 1) *
      Stack.read u (premiere d Z t₀ h (Delay.stones a) (Stack.rise W)) := by
  rw [bank_series,bank_series,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [ray_ticket d Z t u hw hZ h a, vacuum_series d Z u a t hZ h,
    map_mul (Stack.read u), sameFieldOut Z d t t₀ (Delay.stones a) h, mul_assoc]

theorem path_conditional (hZ : LocalRatio Z) (h : d.Room G) (t₀ : d.Tags)
    (J : d.Tags → PathSource (G:=G) d) (hJ : ∀ t g, 0 < g → ∀ V, Measurable (J t g V))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t g, 0 < g → ∀ V x, ‖J t g V x‖ ≤ B)
    (W : SpaceF G d → ℝ) (hc : ∀ t, CommonGerm d (J t) W) (hw : ContDiffAt ℝ ω W 0) :
    Aspiration (rayTotal d u a J / rayTotal d u a 1)
      (term (Stack.read u (premiere d Z t₀ h (Delay.stones a) (Stack.rise W)))) := by
  have expr := Aspiration.sum Finset.univ _ _ fun t _ =>
    path_expansion d h hZ a t u (J t) (hJ t) hB (hb t) W (hc t) hw
  have vac := Aspiration.sum Finset.univ _ _ fun t _ =>
    path_expansion d h hZ a t u 1 (fun _ _ _ => measurable_const) (B:=1) zero_le_one
      (fun _ _ _ _ => by simp) 1 (Eventually.of_forall fun _ _ _ => rfl) contDiffAt_const
  have hpos := vacuum_lead d Z u a hZ h
  have normed : Aspiration (rayTotal d u a J / rayTotal d u a 1)
    (divide (rayBank d Z u a W) (rayBank d Z u a 1)) := expr.quotient vac hpos.ne'
  have hv : constantCoeff (mk (rayBank d Z u a 1)) ≠ 0 := by simpa only [constantCoeff_mk] using hpos.ne'
  have e : Stack.read u (premiere d Z t₀ h (Delay.stones a) (Stack.rise W)) =
      mk (rayBank d Z u a W) * (mk (rayBank d Z u a 1))⁻¹ :=
    (eq_mul_inv_iff_mul_eq hv).mpr ((mul_comm ..).trans (bank_factor d Z u a hZ h t₀ hw).symm)
  rw [e]; exact normed

end YM.Integration.FVA1Physical.Wilson
