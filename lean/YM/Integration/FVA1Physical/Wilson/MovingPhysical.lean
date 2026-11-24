import YM.Integration.FVA1Physical.Wilson.MovingConditional

/-! The actual gauge-invariant conditional path integral at the moving
retained field is expanded in the independently propagated FVA2 reading at
that same direction. No analytic comparison or coefficient identity is
required from the caller. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Function PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FVA2 FVA2.CityHistory
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (u : Pins G c) (a : ℕ → ℝ)

def finePath (O : Config G n → ℝ) : d.Tags → PathSource (G:=G) d :=
  fun _ _ V x => O (d.fine V x)

private theorem fine_total (h : d.OK G) (O : Config G n → ℝ) (hO : Continuous O)
    (hI : GaugeInvariant O) (g : ℝ) :
    rayTotal d u a (finePath d O) g =
      (Real.exp (-1)*(g^Module.finrank ℝ (Coordinates G d))⁻¹*(d.scalar G (offset a g))⁻¹) *
      d.weighted (offset a g) O (expLinks G _ (g • u)) := by
  rw [path_formula h _ hO hI]
  have hS := (scalar_pos G d (offset a g)).ne'
  simp only [rayTotal, Finset.sum_apply,rayReading,pathRegion,setIntegral_univ]
  simp_rw [show ∀ t : d.Tags, pathAmplitude d (offset a g) t (finePath d O t g) (expLinks G _ (g • u)) =
    d.integrand (offset a g) t O (expLinks G _ (g • u)) from fun _ => rfl]
  simp_rw [← Finset.mul_sum]
  field_simp

/-- Physical multi-block reading with its original vacuum, in a nonzero
retained ray, compared to the full Haar/action/offset formal transfer. -/
theorem physical_ray {Z : ChartRatio G} (hZ : LocalRatio Z) (h : d.Room G) (t : d.Tags)
    (O : Config G n → ℝ) (hO : Continuous O) (hI : GaugeInvariant O)
    (hw : ContDiffAt ℝ ω (O ∘ expLinks G (Edge (Site n))) 0) :
    Aspiration (fun g : ℝ => d.conditioned (offset a g) O (expLinks G _ (g • u)))
      (term (Stack.read u (skyread Z d t h (Delay.stones a) (exPay O)))) := by
  let f := finePath d O
  let W := (O ∘ expLinks G (Edge (Site n))) ∘ (placement G d)
  obtain ⟨B,hbound⟩ := isCompact_univ.exists_bound_of_continuousOn (s:=Set.univ) hO.continuousOn
  have hw' : ContDiffAt ℝ ω W 0 := OpenSlots.leaned (placement G d) hw
  have hJ (_ : d.Tags) (_ : ℝ) (_ : Config G c) : Continuous ((finePath d O) ‹_› ‹_› ‹_›) :=
    hO.comp ((fine_continuous d).comp (continuous_const.prodMk continuous_id))
  have hj (t' : d.Tags) : CommonGerm d (f t') W :=
    Eventually.of_forall fun z _ _ => congrArg O (placement_at d z)
  have hj' := path_conditional d Z u a hZ h t f (fun i g _ V => (hJ i g V).measurable)
    (B:=max B 0) (le_max_right ..) (fun _ _ _ _ x => (hbound _ (mem_univ _)).trans (le_max_left ..)) W hj hw'
  have he : Stack.rise W = exValues d O :=
    (FormalOPE.RG10.MarkovChain.Vault.climbing (placement G d) (hw.of_le le_top)).symm
  rw [he] at hj'
  intro k
  obtain ⟨C,hC,P⟩ := hj' k
  refine ⟨C,hC,?_⟩
  filter_upwards [P,eventually_pos] with g price hg
  change ‖(rayTotal d u a f g / rayTotal d u a 1 g) - _‖ ≤ _ at price
  rw [show (1 : d.Tags → PathSource (G:=G) d) = finePath d 1 from rfl,
    fine_total d u a (room_ok d h) O hO hI g,
    fine_total d u a (room_ok d h) 1 continuous_const (fun _ _ => rfl) g,
    mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero (Real.exp_pos _).ne'
      (inv_ne_zero (pow_pos hg _).ne')) (inv_ne_zero (scalar_pos ..).ne')),
    weighted_unit,div_eq_mul_inv,mul_comm (d.weighted ..)] at price
  exact price

end YM.Integration.FVA1Physical.Wilson
