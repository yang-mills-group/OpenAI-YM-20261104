import YM.Comparison.RG02.Assembly.Contact
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Exact coefficients of a continuous normalized ray of a joint analytic germ.
The clearing power is retained as a shift in the derivative order. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualNormalizedRayJets

open Function Filter
open YM.Comparison.RG02.Assembly
open scoped Topology ContDiff

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W]

private lemma jet_eq_coeff {f : ℝ → W}
    {p : FormalMultilinearSeries ℝ ℝ W}
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    jet f n 1 = p.coeff n := by
  obtain ⟨radius, hr⟩ := hp
  change (n.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ n f 0 (fun _ => 1) = p n (fun _ => 1)
  rw [← hr.factorial_smul (1 : ℝ) n,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),
    one_smul]

/-- A continuous extension of the divided ray has the shifted coefficients of
the original analytic germ. Only its punctured germ is used. -/
theorem divided_coefficient {f e : ℝ → W} {B : ℕ}
    (hf : GradeAt B f) (he : ContinuousAt e 0)
    (hvalue : ∀ᶠ t in 𝓝[≠] (0 : ℝ), e t = (t ^ B)⁻¹ • f t)
    (k : ℕ) :
    jet e k 1 = jet f (B + k) 1 := by
  obtain ⟨p, hp⟩ := hf.smooth.analyticAt
  let q : ℝ → W := (Function.swap dslope 0)^[B] f
  have hq : HasFPowerSeriesAt q
      (FormalMultilinearSeries.fslope^[B] p) 0 :=
    HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope B hp
  have hlow : ∀ i < B, (Function.swap dslope 0)^[i] f 0 = 0 := by
    intro i hi
    rw [← (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope i hp).coeff_zero 1]
    change (FormalMultilinearSeries.fslope^[i] p).coeff 0 = 0
    rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
      ← jet_eq_coeff hp i]
    exact hf.jet_z 1 hi
  have hscale (t : ℝ) : t ^ B • q t = f t := by
    simpa only [sub_zero] using
      pow_sub_smul_iterate_dslope_of_zero B hlow t
  have hpunctured : e =ᶠ[𝓝[≠] (0 : ℝ)] q := by
    filter_upwards [hvalue, self_mem_nhdsWithin] with t ht hmem
    have ht0 : t ≠ 0 := by simpa using hmem
    rw [ht, ← hscale t, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero B ht0), one_smul]
  have hzero : e 0 = q 0 :=
    tendsto_nhds_unique
      (he.mono_left nhdsWithin_le_nhds)
      (Filter.Tendsto.congr' hpunctured.symm
        (hq.continuousAt.mono_left nhdsWithin_le_nhds))
  have hfull : e =ᶠ[𝓝 (0 : ℝ)] q := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), e t = q t
    rw [← nhdsNE_sup_pure (0 : ℝ), Filter.eventually_sup,
      Filter.eventually_pure]
    exact ⟨hpunctured, hzero⟩
  calc
    jet e k 1 = jet q k 1 := by
      unfold jet
      rw [(hfull.iteratedFDeriv ℝ k).eq_of_nhds]
    _ = (FormalMultilinearSeries.fslope^[B] p).coeff k :=
      jet_eq_coeff hq k
    _ = p.coeff (k + B) :=
      FormalMultilinearSeries.coeff_iterate_fslope B k
    _ = jet f (k + B) 1 := (jet_eq_coeff hp (k + B)).symm
    _ = jet f (B + k) 1 := by rw [Nat.add_comm k B]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized ray recovers the full joint homogeneous jet on the unit
coupling slice, with its literal clearing-power shift. -/
theorem joint_coefficient {F : ℝ × E → W} {e : ℝ → W} {B : ℕ}
    (hF : GradeAt B F) (A : E) (he : ContinuousAt e 0)
    (hvalue : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      e t = (t ^ B)⁻¹ • F (t, t • A))
    (k : ℕ) :
    jet e k 1 = jet F (B + k) (1, A) := by
  let L : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.toSpanSingleton ℝ (1, A)
  have hsource : F ∘ L = fun t : ℝ => F (t, t • A) := by
    funext t
    simp [L]
  have hgrade : GradeAt B (F ∘ L) :=
    hF.coarse L.contDiff.contDiffAt L.map_zero
  have hv : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      e t = (t ^ B)⁻¹ • (F ∘ L) t := by
    simpa only [hsource] using hvalue
  calc
    jet e k 1 = jet (F ∘ L) (B + k) 1 :=
      divided_coefficient hgrade he hv k
    _ = jet F (B + k) (1, A) := by
      simpa [L] using
        jet_continuous_right L (hF.smooth.of_le le_top) (1 : ℝ)

end YM.Integration.ActualNormalizedRayJets
end
