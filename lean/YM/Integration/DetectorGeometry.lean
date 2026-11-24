import YM.OPE.Detector
import YM.OPE.Exchange.Regime

/-! Positive macroscopic clearance for the actual finite physical detector.
The clearance is chosen before the shrinking input configuration. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration
open Function Filter Set OPE
open scoped Topology Classical

private lemma finite_positive_floor {I : Type*} [Finite I]
    (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ a i := by
  have h : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i, δ ≤ a i := by
    apply eventually_all.mpr
    intro i
    exact ((gt_mem_nhds (ha i)).filter_mono nhdsWithin_le_nhds).mono
      (fun _ hi => hi.le)
  exact ((show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and h).exists

variable {G : Gauge} {L : Register G} {S : Table L}

/-- Every actual admissible exterior has a fixed positive clearance from the
origin and between all its own points, including the empty exterior. -/
theorem detector_exterior_clearance (E : ExteriorData S) (hE : Apt E) :
    ∃ δ : ℝ, 0 < δ ∧ ClearOf 0 (positions S E).ofLp δ := by
  let z := Points.cons 0 (positions S E)
  have hz : Injective z.ofLp := generic_conf _ hE
  let a : Fin (E.length + 1) × Fin (E.length + 1) → ℝ :=
    fun p => if p.1 = p.2 then 1 else ‖z p.1 - z p.2‖
  have ha : ∀ p, 0 < a p := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [a, hp]
    · simp only [a, if_neg hp]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (hz.ne hp))
  obtain ⟨δ, hδ, hd⟩ := finite_positive_floor a ha
  refine ⟨δ, hδ, ⟨?_, ?_⟩⟩
  · intro i
    have ht := hd (0, i.succ)
    simp only [a, if_neg (Ne.symm (Fin.succ_ne_zero i))] at ht
    exact ht
  · intro i j hij
    have ht := hd (i.succ, j.succ)
    simp only [a, if_neg (fun h => hij (Fin.succ_injective _ h))] at ht
    exact ht

/-- A single positive clearance works for every exterior in the chosen finite
detector. Its value does not depend on the input fields or shrinking length. -/
theorem detector_uniform_clearance {D : ℕ} (U : Detector S D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, ClearOf 0 (positions S (U.listen i)).ofLp δ := by
  choose a ha hc using fun i => detector_exterior_clearance (U.listen i) (U.awake i)
  obtain ⟨δ, hδ, hd⟩ := finite_positive_floor a ha
  refine ⟨δ, hδ, fun i => ⟨fun j => ?_, fun j k hjk => ?_⟩⟩
  · exact (hd i).trans ((hc i).openSpace j)
  · exact (hd i).trans ((hc i).spread j k hjk)

end YM.Integration
