import YM.Integration.ActualNormalizedRayJets
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.LeftRight

/-! Finite jets of a positive-side normalized ray. The supplied extension is
only smooth through the requested order. The analytic numerator supplies the
canonical divided germ; no analytic continuation of the extension is assumed.
The clearing power remains in the exact B+k coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PositiveNormalizedRayJets

open Function Filter Set
open Comparison.RG02.Assembly
open scoped Topology ContDiff

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W]

omit [CompleteSpace W] in
private lemma positive_jet {f g : ℝ → W} {k : ℕ}
    (hf : ContDiffAt ℝ k f 0) (hg : ContDiffAt ℝ k g 0)
    (he : f =ᶠ[𝓝[>] (0 : ℝ)] g) : jet f k 1 = jet g k 1 := by
  have hzero : f 0 = g 0 := tendsto_nhds_unique
    (hf.continuousAt.mono_left nhdsWithin_le_nhds)
    (Filter.Tendsto.congr' he.symm
      (hg.continuousAt.mono_left nhdsWithin_le_nhds))
  have hclosed : f =ᶠ[𝓝[Ici (0 : ℝ)] 0] g := by
    change ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, f t = g t
    rw [← Ioi_insert, nhdsWithin_insert, Filter.eventually_sup,
      Filter.eventually_pure]
    exact ⟨hzero, he⟩
  have hd : iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0 := by
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0) hf
        (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr le_rfl),
      ← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici 0) hg
        (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr le_rfl)]
    exact hclosed.iteratedFDerivWithin_eq hzero k
  unfold jet
  rw [hd]

-- The coefficient and canonical-quotient steps below are the unchanged
-- native power-series argument from ActualNormalizedRayJets; only the final
-- comparison with the supplied extension uses a positive-side finite jet.
private lemma jet_eq_coeff {f : ℝ → W}
    {p : FormalMultilinearSeries ℝ ℝ W}
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) : jet f n 1 = p.coeff n := by
  obtain ⟨radius, hr⟩ := hp
  change (n.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ n f 0 (fun _ => 1) = p n (fun _ => 1)
  rw [← hr.factorial_smul (1 : ℝ) n, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),
    one_smul]

theorem divided_coefficient {f e : ℝ → W} {B k : ℕ}
    (hf : GradeAt B f) (he : ContDiffAt ℝ k e 0)
    (hvalue : ∀ᶠ t in 𝓝[>] (0 : ℝ), e t = (t ^ B)⁻¹ • f t) :
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
    rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add, ← jet_eq_coeff hp i]
    exact hf.jet_z 1 hi
  have hscale (t : ℝ) : t ^ B • q t = f t := by
    simpa only [sub_zero] using pow_sub_smul_iterate_dslope_of_zero B hlow t
  have hpositive : e =ᶠ[𝓝[>] (0 : ℝ)] q := by
    filter_upwards [hvalue, self_mem_nhdsWithin] with t ht hmem
    have ht0 : t ≠ 0 := (show 0 < t from hmem).ne'
    rw [ht, ← hscale t, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero B ht0), one_smul]
  have hqSmooth : ContDiffAt ℝ k q 0 :=
    (show AnalyticAt ℝ q 0 from ⟨_, hq⟩).contDiffAt
  calc
    jet e k 1 = jet q k 1 := positive_jet he hqSmooth hpositive
    _ = (FormalMultilinearSeries.fslope^[B] p).coeff k := jet_eq_coeff hq k
    _ = p.coeff (k + B) := FormalMultilinearSeries.coeff_iterate_fslope B k
    _ = jet f (k + B) 1 := (jet_eq_coeff hp (k + B)).symm
    _ = jet f (B + k) 1 := by rw [Nat.add_comm k B]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_coefficient {F : ℝ × E → W} {e : ℝ → W} {B k : ℕ}
    (hF : GradeAt B F) (A : E) (he : ContDiffAt ℝ k e 0)
    (hvalue : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      e t = (t ^ B)⁻¹ • F (t, t • A)) :
    jet e k 1 = jet F (B + k) (1, A) := by
  let L : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.toSpanSingleton ℝ (1, A)
  have hsource : F ∘ L = fun t : ℝ => F (t, t • A) := by
    funext t
    simp [L]
  have hgrade : GradeAt B (F ∘ L) :=
    hF.coarse L.contDiff.contDiffAt L.map_zero
  have hv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      e t = (t ^ B)⁻¹ • (F ∘ L) t := by
    simpa only [hsource] using hvalue
  calc
    jet e k 1 = jet (F ∘ L) (B + k) 1 := divided_coefficient hgrade he hv
    _ = jet F (B + k) (1, A) := by
      simpa [L] using jet_continuous_right L (hF.smooth.of_le le_top) (1 : ℝ)

end YM.Integration.PositiveNormalizedRayJets
end
