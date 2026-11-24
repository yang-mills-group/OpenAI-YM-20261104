import YM.Integration.WilsonWholeLimit

/-! The fixed physical detector stays separated from every sufficiently
small input room. The geometric threshold is chosen before the input
fields, running frame, and comparison field. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonWholeLimit

open Function Filter Set OPE
open scoped Classical Topology

private lemma room_beside {I J : Type} {x : I → E4} {y : J → E4}
    {o : E4} {r M η δ : ℝ} (hr : 0 < r) (hη : 0 < η) (hδ : 0 < δ)
    (hs : M * r < δ) (hx : WithinRoom r M η x o) (hy : ClearOf o y δ) :
    Injective (beside x y) := by
  have hxi : Injective x := by
    intro i j hij
    by_contra hne
    have h := hx.spaced i j hne
    rw [hij, sub_self, norm_zero] at h
    exact (not_le_of_gt (mul_pos hη hr)) h
  have hyi : Injective y := by
    intro i j hij
    by_contra hne
    have h := hy.spread i j hne
    rw [hij, sub_self, norm_zero] at h
    exact (not_le_of_gt hδ) h
  have hxy : ∀ i j, x i ≠ y j := by
    intro i j hij
    have h := hx.span i
    rw [hij, norm_sub_rev] at h
    exact (not_le_of_gt hs) ((hy.openSpace j).trans h)
  rintro (i | i) (j | j) hij
  · exact congr_arg Sum.inl (hxi hij)
  · exact (hxy i j hij).elim
  · exact (hxy j i hij.symm).elim
  · exact congr_arg Sum.inr (hyi hij)

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (H : Spec.Final C f S) {I : Type} [Fintype I]

omit [Fintype I] in
/-- One geometric threshold works for all input configurations and every
exterior of the original finite detector. -/
theorem detector_separated_in_room {D : ℕ} (U : Detector S D)
    (M η : ℝ) (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x : I → E4, WithinRoom r M η x 0 →
      ∀ i, Injective (beside x (positions S (U.listen i)).ofLp) := by
  obtain ⟨δ, hδ, hc⟩ := detector_uniform_clearance U
  have ht : Tendsto (fun r : ℝ => M * r) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun r : ℝ => M * r) (𝓝[>] 0) (𝓝 (M * 0)))
  filter_upwards [show ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r from self_mem_nhdsWithin,
    ht.eventually (gt_mem_nhds hδ)] with r hr hs x hx i
  exact room_beside hr hη hδ hs hx (hc i)

include H in
/-- On the ordinary shrinking room, the literal finite discrepancy has
the required continuum limit for every subsequently chosen frame and
comparison field. No rate of this regulator limit is asserted. -/
theorem wholeReadout_discrepancy_tendsto_in_room (hS : Services C f S)
    {D : ℕ} (U : Detector S D) (M η : ℝ) (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x : I → E4, WithinRoom r M η x 0 →
      ∀ (A : ℝ → PhysMS.tower S) (d : I → ℕ)
        (v : ∀ i, (Climb.Bel C.book).Field (d i)) (z : S.Field D),
        Tendsto (fun q : ℕ × ℕ => EngineeringWeightedReadout.wholeReadout U A r
          (fun i => Wilson.moment (C.beta q.1 q.2)
            (detectorDiscrepancy A U v r x z q.1 q.2 i)))
          f.fuse (𝓝 (EngineeringWeightedReadout.wholeReadout U A r
            (PhysicalMSOPEReadout.candidateResidual A U v r x z))) := by
  filter_upwards [detector_separated_in_room (I := I) U M η hη] with r hr x hx A d v z
  exact wholeReadout_discrepancy_tendsto H hS A U v r x z (hr x hx)

include H in
/-- The same geometric threshold allows any proved eventual finite-law
bound to pass to the exact continuum candidate residual. -/
theorem wholeReadout_discrepancy_le_in_room (hS : Services C f S)
    {D : ℕ} (U : Detector S D) (M η : ℝ) (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x : I → E4, WithinRoom r M η x 0 →
      ∀ (A : ℝ → PhysMS.tower S) (d : I → ℕ)
        (v : ∀ i, (Climb.Bel C.book).Field (d i)) (z : S.Field D) (b : ℝ),
        (∀ᶠ q : ℕ × ℕ in f.fuse,
          ‖EngineeringWeightedReadout.wholeReadout U A r
            (fun i => Wilson.moment (C.beta q.1 q.2)
              (detectorDiscrepancy A U v r x z q.1 q.2 i))‖ ≤ b) →
        ‖EngineeringWeightedReadout.wholeReadout U A r
          (PhysicalMSOPEReadout.candidateResidual A U v r x z)‖ ≤ b := by
  filter_upwards [detector_separated_in_room (I := I) U M η hη] with r hr x hx A d v z b hb
  exact wholeReadout_discrepancy_le H hS A U v r x z (hr x hx) b hb

end YM.Integration.WilsonWholeLimit
