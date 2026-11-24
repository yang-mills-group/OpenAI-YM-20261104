import YM.Integration.FVA1Physical.Wilson.LeadingMass

/-! A genuinely varying RG clock need only have the right leading scale at
each level for the inherited reduced quadratic to survive. The proof uses
two honest finite-coupling integrals on neighboring scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Function MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent FormalOPE.RG10.OpenSlots
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested FVA2.CityHistory
open scoped Classical Topology
variable {G : Gauge} {n c : Side} (d : Descent n c) (Z : ChartRatio G) (t : d.Tags)
    (h : d.Room G) (hZ : LocalRatio Z) (u : Pins G c)

private def dialLimit (s : ℝ) : ℝ := (s^Module.finrank ℝ (Coordinates G d))⁻¹ *
  ((∑ q, rayFactor d Z q 0 h) * rayGaussian d t h (s • u))

private theorem dial_cont : ContinuousAt (dialLimit d Z t h u) 1 := by
  have op (s : ℝ) : rayGaussian d t h (s • u) =
      Real.exp (-(s*(s*(retained d t h).flourish u))/2) := by
    simp [rayGaussian,Quadratic.flourish,map_smul,LinearMap.smul_apply,smul_eq_mul]
  change ContinuousAt (fun s : ℝ => (s^Module.finrank ℝ (Coordinates G d))⁻¹ *
    ((∑ q, rayFactor d Z q 0 h) * rayGaussian d t h (s • u))) 1
  simp_rw [op]
  fun_prop (disch := positivity)

include hZ
private theorem closest_mass (s : ℝ) (hs : 0 < s) :
    Tendsto (fun g => scaledMass d (scalarClock s g) u g) Tested.germ (𝓝 (dialLimit d Z t h u s)) := by
  have step : Tendsto (fun g : ℝ => g/s) Tested.germ Tested.germ := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,eventually_pos.mono fun g hg => div_pos hg hs⟩
    simpa only [id_eq,zero_div] using ((continuous_id.div_const s).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have H := ((absolute_limit d Z t h hZ (s • u)).comp step).const_mul
    (s^Module.finrank ℝ (Coordinates G d))⁻¹
  exact H.congr' (Eventually.of_forall fun g => (dial_mass d u s hs g).symm)

theorem changing_absolute (β : ℝ → ℕ → ℝ)
    (slope : ∀ i ≤ d.depth, Tendsto (fun g : ℝ => g^2*β g i) Tested.germ (𝓝 1)) :
    Tendsto (fun g => scaledMass d (β g) u g) Tested.germ
      (𝓝 ((∑ q, rayFactor d Z q 0 h)*rayGaussian d t h u)) := by
  let A := dialLimit d Z t h u
  have home : A 1 = (∑ q, rayFactor d Z q 0 h)*rayGaussian d t h u := by simp [A,dialLimit]
  rw [← home]
  have monotone {b e : ℕ → ℝ} (g : ℝ) (hg : 0<g) (H : ∀ i ≤ d.depth, b i ≤ e i) :
      scaledMass d e u g ≤ scaledMass d b u g :=
    mul_le_mul_of_nonneg_left (mass_antitone d (room_ok d h) H _) (mul_nonneg
      (Real.exp_pos _).le (inv_nonneg.mpr (pow_nonneg hg.le _)))
  apply tendsto_order.mpr
  constructor
  · intro v hv
    have right : ∀ᶠ s : ℝ in 𝓝[>] 1, 1<s := self_mem_nhdsWithin
    have nearOne : ∀ᶠ s : ℝ in 𝓝 1, v < A s := (dial_cont d Z t h u).eventually (lt_mem_nhds hv)
    obtain ⟨s,hs,near⟩ := (right.and (nearOne.filter_mono nhdsWithin_le_nhds)).exists
    have hs' : 1<s := hs
    have hs0 : 0<s := zero_lt_one.trans hs'
    have hsq : 1<s^2 := by nlinarith
    have all := eventually_all.mpr (fun i : Fin (d.depth+1) =>
      (slope i.val (Nat.le_of_lt_succ i.isLt)).eventually (gt_mem_nhds hsq))
    filter_upwards [eventually_pos,all,(closest_mass d Z t h hZ u s hs0).eventually (lt_mem_nhds near)]
      with g hg H enough
    apply enough.trans_le (monotone g hg ?_)
    intro i hi
    have hi' := (H ⟨i,Nat.lt_succ_of_le hi⟩).le
    change β g i ≤ (s/g)^2
    rw [div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hg)).mpr (by simpa only [mul_comm] using hi')
  · intro v hv
    have left : ∀ᶠ s : ℝ in 𝓝[<] 1, s<1 := self_mem_nhdsWithin
    have nearOne : ∀ᶠ s : ℝ in 𝓝 1, A s < v := (dial_cont d Z t h u).eventually (gt_mem_nhds hv)
    have pos : ∀ᶠ s : ℝ in 𝓝 1, 0<s := lt_mem_nhds zero_lt_one
    obtain ⟨s,hs,hp,near⟩ := (left.and ((pos.and nearOne).filter_mono nhdsWithin_le_nhds)).exists
    have hs' : s<1 := hs
    have hs0 : 0<s := hp
    have hsq : s^2<1 := by nlinarith [mul_pos hs0 (sub_pos.mpr hs')]
    have all := eventually_all.mpr (fun i : Fin (d.depth+1) =>
      (slope i.val (Nat.le_of_lt_succ i.isLt)).eventually (lt_mem_nhds hsq))
    filter_upwards [eventually_pos,all,(closest_mass d Z t h hZ u s hs0).eventually (gt_mem_nhds near)]
      with g hg H enough
    apply lt_of_le_of_lt (monotone g hg ?_) enough
    intro i hi
    have hi' := (H ⟨i,Nat.lt_succ_of_le hi⟩).le
    change (s/g)^2 ≤ β g i
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hg)).mpr (by simpa only [mul_comm] using hi')

theorem changing_centered (β : ℝ → ℕ → ℝ)
    (slope : ∀ i ≤ d.depth, Tendsto (fun g : ℝ => g^2*β g i) Tested.germ (𝓝 1)) :
    Tendsto (fun g : ℝ => d.vacuum (β g) (expLinks G _ (g • u)) / d.vacuum (G:=G) (β g) 1)
      Tested.germ (𝓝 (rayGaussian d t h u)) := by
  let M := ∑ q, rayFactor d Z q 0 h
  have hM : 0<M := Finset.sum_pos (fun q _ => rayFactor_pos d Z q 0 hZ h) Finset.univ_nonempty
  have base := changing_absolute d Z t h hZ 0 β slope
  rw [rayGaussian_zero,mul_one] at base
  have H := (changing_absolute d Z t h hZ u β slope).div base hM.ne'
  rw [mul_div_cancel_left₀ _ hM.ne'] at H
  apply H.congr'
  filter_upwards [eventually_pos] with g hg
  change scaledMass d (β g) u g / scaledMass d (β g) 0 g = _
  rw [scaledMass,scaledMass,mul_div_mul_left _ _ (mul_ne_zero (Real.exp_pos _).ne'
    (inv_ne_zero (pow_pos hg _).ne')),smul_zero,FormalOPE.RG10.Inherit.identity_zero,
    mass_density d (room_ok d h) (β g) _,mass_density d (room_ok d h) (β g) 1,
    mul_div_mul_left _ _ (scalar_pos ..).ne']

end YM.Integration.FVA1Physical.Wilson
