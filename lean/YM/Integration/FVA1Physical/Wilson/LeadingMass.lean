import YM.Integration.FVA1Physical.Wilson.MovingVacuumBank

/-! Absolute physical masses on a retained ray at possibly different
inverse couplings. Monotonicity and rescaling use the full nonlinear action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent Push.BetaTransport
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)

def massAt (β : ℕ → ℝ) (U : Config G c) : ℝ :=
  ∑ t : d.Tags, ∫ x, d.integrand β t 1 U x ∂d.measure G

theorem mass_density (h : d.OK G) (β : ℕ → ℝ) (U : Config G c) :
    d.vacuum β U = d.scalar G β * massAt d β U := by
  rw [← weighted_unit]
  exact path_formula h β (g:=1) continuous_const (fun _ _ => rfl) U

private theorem charge_mono {β γ : ℕ → ℝ} (H : ∀ i ≤ d.depth, β i ≤ γ i)
    (t : d.Tags) (V : Config G c) (x : Fields G d) :
    d.account β t V x ≤ d.account γ t V x := by
  induction d generalizing β γ with
  | nil => exact mul_le_mul_of_nonneg_right (H 0 le_rfl) (energy_nonneg ..)
  | push S T p ih =>
    rw [account,account]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (H 1 (Nat.succ_le_succ (Nat.zero_le _))) ((energy_estimate S _).nonneg _)
    · exact ih (fun i hi => H (i+1) (Nat.succ_le_succ hi)) _ _ _

theorem mass_antitone (h : d.OK G) {β γ : ℕ → ℝ} (H : ∀ i ≤ d.depth, β i ≤ γ i)
    (V : Config G c) : massAt d γ V ≤ massAt d β V := by
  unfold massAt
  apply Finset.sum_le_sum
  intro t _
  apply integral_mono (path_integrable h γ t 1 continuous_const V) (path_integrable h β t 1 continuous_const V)
  intro x
  simp only [integrand,Pi.one_apply,mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (charge_mono d H t V x)))
    (probability_nonneg d t x)

def scaledMass (β : ℕ → ℝ) (u : Pins G c) (g : ℝ) : ℝ :=
  Real.exp (-1) * (g^Module.finrank ℝ (Coordinates G d))⁻¹ * massAt d β (expLinks G _ (g • u))

theorem scale_fixed_mass (u : Pins G c) (a : ℕ → ℝ) (g : ℝ) :
    rayTotal d u a 1 g = scaledMass d (offset a g) u g := by
  simp only [rayTotal,Finset.sum_apply,rayReading,pathRegion,setIntegral_univ,scaledMass,massAt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc]
  rfl

def scalarClock (s g : ℝ) (_ : ℕ) : ℝ := (s/g)^2

theorem dial_mass (u : Pins G c) (s : ℝ) (hs : 0 < s) (g : ℝ) :
    scaledMass d (scalarClock s g) u g =
      (s^Module.finrank ℝ (Coordinates G d))⁻¹ * rayTotal d (s • u) 0 1 (g/s) := by
  rw [scale_fixed_mass]
  have hc : offset (0:ℕ→ℝ) (g/s) = scalarClock s g := by
    funext i
    simp [offset,scalarClock,inv_div]
  simp only [scaledMass,hc,smul_smul,div_mul_cancel₀ _ hs.ne',div_pow,inv_div]
  field_simp

theorem absolute_limit (Z : ChartRatio G) (t : d.Tags) (h : d.Room G) (hZ : LocalRatio Z) (u : Pins G c) :
    Tendsto (rayTotal d u 0 1) Tested.germ (𝓝 ((∑ s, rayFactor d Z s 0 h)*rayGaussian d t h u)) := by
  have H : Aspiration (rayTotal d u 0 1) (rayBank d Z u 0 1) :=
    Aspiration.sum Finset.univ _ _ fun s _ => path_expansion d h hZ 0 s u 1
      (fun _ _ _ => measurable_const) (B:=1) zero_le_one (fun _ _ _ _ => by simp)
      1 (Eventually.of_forall fun _ _ _ => rfl) contDiffAt_const
  have e : rayBank d Z u 0 1 0 = (∑ s,rayFactor d Z s 0 h)*rayGaussian d t h u := by
    rw [← PowerSeries.coeff_mk 0 (rayBank d Z u 0 1),PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ray_bank_absolute d Z t h 0 u hZ,map_mul,map_mul,PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_C,ray_den_constant d Z t h 0 u hZ,mul_one]
  exact e ▸ H.tendsto_first

end YM.Integration.FVA1Physical.Wilson
