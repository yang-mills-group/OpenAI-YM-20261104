import YM.Integration.FVA1Physical.Wilson.ContinuedPrice
import YM.RGComparison.Core16.Laplace

/-! Quantitative separation of exceptional history fields with a nontrivial
retained boundary. The same gap works for all positive-likelihood tags and
all boundary fields whose individual link chords stay below the allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set RG Lattice YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart FVA2.CityHistory FormalOPE.RG10.Inherit
open scoped Classical Topology

theorem moving_barrier {G : Gauge} {n c : Side} (d : Descent n c) (h : d.Room G)
    (Z : ChartRatio G) {r : ℝ} (hr : 0 < r) (hZr : r ≤ small G Z) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ (V : Config G c), QuietLinks V ε →
      ∀ (t : d.Tags) (x : Fields G d), x ∉ chamber G d.Links r → 0 < d.probability t x →
        K ≤ d.action t V x := by
  obtain ⟨b,hb,wall⟩ := wall_bound Z hr hZr
  let e := d.edgeBill G
  let K := (b/2/(1+e))^2
  have he : 0 ≤ e := edgeBill_nonneg G d
  have hz : 0 < 1+e := by positivity
  refine ⟨b/2,K,half_pos hb,pow_pos (div_pos (half_pos hb) hz) _,?_⟩
  intro V v t x outside ht
  obtain ⟨i,hi⟩ : ∃ i, x i ∈ exteriorLinks (G:=G) r := by
    by_contra! H
    exact outside fun i _ => not_not.mp (H i)
  let E := d.action t V x
  have hE : 0 ≤ E := action_nonneg ..
  have edge := controls_links (Real.sqrt_nonneg E) ht (Real.sq_sqrt hE).symm.le
    h v (half_pos hb).le i
  have scale : b/2/(1+e) ≤ Real.sqrt E := by
    apply (div_le_iff₀ hz).mpr
    change G.chord (x i) ≤ e * Real.sqrt E + b/2 at edge
    nlinarith only [edge,wall (x i) hi,Real.sqrt_nonneg E]
  exact (pow_le_pow_left₀ (div_nonneg (half_pos hb).le hz.le) scale 2).trans_eq (Real.sq_sqrt hE)

/-- Every fixed retained Lie-algebra direction enters the allowance on
its entire sufficiently small physical Haar ray. -/
theorem moving_ray_quiet {G : Gauge} {c : Side} (u : Pins G c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : ℝ in 𝓝 0, QuietLinks (expLinks G _ (g • u)) ε := by
  apply Filter.eventually_all.mpr
  intro e
  have he : Continuous (fun g : ℝ => G.chord (G.lieExp (g • u e))) :=
    G.continuous_chord.comp (G.lieExp_cont.comp (continuous_id.smul continuous_const))
  have ht : Tendsto (fun g : ℝ => G.chord (G.lieExp (g • u e))) (𝓝 0) (𝓝 0) := by
    simpa using he.tendsto 0
  exact (ht.eventually (gt_mem_nhds hε)).mono fun g hg => le_of_lt hg

end YM.Integration.FVA1Physical.Wilson
