import YM.Integration.WilsonRenderedScalarReturn
import YM.Integration.ActualWilsonAbsoluteTransport

/-! Integrate the entire signed observation, with one common protected event,
against the original Wilson marginal before returning to any earlier age. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointAxialAbsolute
open MeasureTheory Filter Lattice RG Wilson Ac Marker QuadraticLocal Multi
open PhysicalNext.Repeat.Legato WilsonLimitConstruction OPE.Therm
open scoped Classical BigOperators Topology

private theorem addRows {S X : Type*} (faces : Finset S) (c : S → ℂ)
    (a : S → X → ℂ) (cost : S → ℝ) (U : X) (bound : ∀ s ∈ faces, ‖a s U‖ ≤ cost s) :
    ‖∑ s∈faces,c s * a s U‖ ≤ ∑ s∈faces,‖c s‖ * cost s :=
  (norm_sum_le _ _).trans <| Finset.sum_le_sum fun s hs => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (bound s hs) (norm_nonneg _)

theorem older {G : Gauge} (R : Run G) {i N p : ℕ} (live : i ≤ N)
    {S : Type*} (faces : Finset S) (c : S → ℂ)
    (C : Set (Config G (R.family.side i p))) (mc : MeasurableSet C)
    (actual finite : S → Config G (R.family.side i p) → ℂ)
    (ma : ∀ s ∈ faces, Measurable (actual s)) (mf : ∀ s ∈ faces, Measurable (finite s))
    (paid gross : S → ℝ) (hp : ∀ s ∈ faces, 0 ≤ paid s) (hg : ∀ s ∈ faces, 0 ≤ gross s)
    (protectedRows : ∀ U ∈ C, ∀ s ∈ faces, ‖actual s U - finite s U‖ ≤ paid s)
    (stock : ∀ U, ∀ s ∈ faces, ‖actual s U‖ ≤ gross s) :
    let f := fun U => ∑ s∈faces,c s * (actual s U - C.indicator (finite s) U)
    let δ := ∑ s∈faces,‖c s‖ * paid s
    let M := ∑ s∈faces,‖c s‖ * gross s
    ∀ u, (h : u ≤ i) →
      ∫ U, ‖actualTransport R.family (N:=N) f h U‖ ∂scene R.family.path N p u ≤
        δ + (scene R.family.path N p i).real Cᶜ * M := by
  intro f δ M u h
  let μ := scene R.family.path N p i
  letI : IsProbabilityMeasure μ := OPE.Therm.probability (H:=R.family.path) (p:=p) R.makes.wilson live
  have nd : 0 ≤ δ := Finset.sum_nonneg fun s hs => mul_nonneg (norm_nonneg _) (hp s hs)
  have nm : 0 ≤ M := Finset.sum_nonneg fun s hs => mul_nonneg (norm_nonneg _) (hg s hs)
  have measurable : Measurable f := Finset.measurable_sum _ fun s hs =>
    measurable_const.mul ((ma s hs).sub ((mf s hs).indicator mc))
  have good (U) (uc : U ∈ C) : ‖f U‖ ≤ δ := by
    refine addRows faces c (fun s A => actual s A - C.indicator (finite s) A) paid U ?_
    intro s hs
    simpa only [Set.indicator_of_mem uc] using protectedRows U uc s hs
  have bad (U) (uc : U ∉ C) : ‖f U‖ ≤ M := by
    refine addRows faces c (fun s A => actual s A - C.indicator (finite s) A) gross U ?_
    intro s hs
    simpa only [Set.indicator_of_notMem uc,sub_zero] using stock U s hs
  have envelope : RG.Envelope f := ⟨measurable,δ+M,fun U => by
    by_cases uc : U ∈ C
    · exact (good U uc).trans (le_add_of_nonneg_right nm)
    · exact (bad U uc).trans (le_add_of_nonneg_left nd)⟩
  have si : Integrable f μ := (integrable_const (μ:=μ) (δ+M)).mono' measurable.aestronglyMeasurable
    (Eventually.of_forall fun U => by
      by_cases uc : U ∈ C
      · exact (good U uc).trans (le_add_of_nonneg_right nm)
      · exact (bad U uc).trans (le_add_of_nonneg_left nd))
  let surcharge := Cᶜ.indicator (fun _ => M)
  have extra : Integrable surcharge μ := (integrable_const (μ:=μ) M).indicator mc.compl
  calc
    _ ≤ ∫ U, ‖f U‖ ∂μ := ActualWilsonAbsoluteTransport.first R.family R.makes live
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes live envelope) h
    _ ≤ ∫ U, δ+surcharge U ∂μ := by
      apply integral_mono si.norm ((integrable_const δ).add extra)
      intro U
      change ‖f U‖ ≤ δ + surcharge U
      by_cases uc : U ∈ C
      · simpa only [surcharge,Set.indicator_of_notMem (show U ∉ Cᶜ from fun hc => hc uc), add_zero] using good U uc
      · simpa only [surcharge,Set.indicator_of_mem (show U ∈ Cᶜ from uc)] using
          (bad U uc).trans (le_add_of_nonneg_left nd)
    _ = _ := by
      rw [integral_add (integrable_const δ) extra,integral_const,probReal_univ,one_smul,
        show (∫ U,surcharge U ∂μ) = μ.real Cᶜ*M from integral_indicator_const M mc.compl]

end YM.Integration.WilsonJointAxialAbsolute
