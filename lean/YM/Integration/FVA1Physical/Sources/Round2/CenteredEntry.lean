import YM.Integration.FVA1Physical.Sources.Round2.CurrentRegularExterior

/-! A scalar physical coefficient has only its constant and absolutely
rooted regular rows in the exponential entry. This controls its contribution
on the complement of a localized posterior chart. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels
open Push Push.AbsoluteSums LocalLTE.Concourse
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} {F₀:Frame G 0} {R:Rep G n}

theorem empty_share (Q:Coefficient F n) (U:Config G n) (clear:flags R.p.threshold U=∅) :
    forcedShare Q R U=0 := by
  have kill (a:Finset ℕ):Q.marked R a U=0:=by
    unfold Coefficient.marked
    split
    next h =>
      have empty:a=∅:=by
        by_contra ne
        obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr ne
        have included: (R.activities.forced i).inventory ⊆ a.biUnion (fun j=>(R.activities.forced j).inventory) :=
          subset_biUnion_of_mem (fun j=>(R.activities.forced j).inventory) hi
        rw [h.2,clear] at included
        exact (R.activities.forced i).inventory_ne.ne_empty (subset_empty.mp included)
      subst a;simp
    next => rfl
  simp only [forcedShare,kill,tsum_zero,zero_div]

theorem centered_entry (Q:Coefficient F₀ n) {z:Site n} {A:Hol G} (shape:Q.Format z A R)
    {κ c:ℝ} (fund:Q.remBound z R κ c) (D:SectionData F₀) :
    let E:=Q.exponentialEntry z D R
    E 1=Q.x 0 ∧ Measurable E ∧ GaugeInvariant E ∧ ∀U,‖E U-Q.x 0‖ ≤ c := by
  intro E
  have eq : E=(fun U=>Q.x 0+∑' i,Q.maskedTerm R i U) := funext (center_entry D Q R z)
  rw [eq]
  have zero (i):Q.maskedTerm R i 1=0:=by
    by_cases clean:Healthy R.p.threshold (Q.support i) (1:Config G n)
    · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ clean,shape.identity_null]
    rw [Coefficient.maskedTerm,masked_ne _ _ _ _ clean]
  have integr (i):Measurable (Q.maskedTerm R i):=masked_measurable _ _ _ (shape.smooth i).borel
  have sym (i):GaugeInvariant (Q.maskedTerm R i):=by
    intro k U
    have same : Healthy R.p.threshold (Q.support i) (gauge k U) ↔ Healthy R.p.threshold (Q.support i) U := by
      unfold Healthy;rw [gauge_flags]
    by_cases h:Healthy R.p.threshold (Q.support i) U
    · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ (same.mpr h),masked_eq _ _ _ _ h,(shape.smooth i).symmetry]
    rw [Coefficient.maskedTerm,masked_ne _ _ _ _ (mt same.mp h),masked_ne _ _ _ _ h]
  have g (k U) : (fun i=>Q.maskedTerm R i (gauge k U))=(fun i=>Q.maskedTerm R i U) := funext (fun i=>sym i k U)
  refine ⟨by simp only [zero,tsum_zero,add_zero],measurable_const.add (Measurable.tsum integr),fun k U=>by dsimp only;rw [g k U],?_⟩
  intro U
  rw [add_sub_cancel_left]
  obtain ⟨a,b,_,bn,tot,_,⟨w,paid,cost⟩,_⟩:=fund
  have cap (i):‖Q.maskedTerm R i U‖≤w i:=by
    by_cases h:Healthy R.p.threshold (Q.support i) U
    · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ h]
      exact (cost i).2 U h [] (Nat.zero_le _) (by simp)
    rw [Coefficient.maskedTerm,masked_ne _ _ _ _ h,norm_zero]
    exact (cost i).1
  have pay:=budget_mono paid (fun i=>norm_nonneg (Q.maskedTerm R i U))
    (fun i=>(cap i).trans (R.p.loMass _ _ (cost i).1))
  exact (norm_tsum_le_tsum_norm pay.2.1).trans (pay.2.2.trans (by linarith only [bn,tot]))

end YM.Integration.FVA1Physical.Round2.Curvature
