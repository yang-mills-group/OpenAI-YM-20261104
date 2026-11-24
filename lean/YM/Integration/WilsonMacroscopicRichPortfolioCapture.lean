import YM.Integration.WilsonMacroscopicRichGradedCalendar

/-! One positive output coefficient holds every signed member of the physical source before transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichPortfolioCapture
open Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG16.Literal Push GridApprox Trace.Physical.GermGraph
open scoped BigOperators Classical
variable {G:Gauge}(C:Family G)(N p h b:ℕ)(H:C.Makes) {I:Type} [Fintype I]
local notation "F" => C.labels.level h
local notation "R!" => C.path.rep N p b
local notation "S!" => C.localSection h

include H in
theorem merged (start:C.ref h ≤ b)(live:b ≤ N)(w:I → ℂ) (f:I → Cut C N p) (cont:∀i,Continuous (f i))
    (r:I → ℝ)(K:I → Coefficient F (C.side b p))
    (row:∀i,(K i).Format 0 C.params R! ∧ (K i).remBound 0 R! (safety C b) (r i) ∧
      (F).coeffSize (K i).x ≤ r i ∧ credit C N p h (f i) b live=(K i).density 0 S! R!):
    ∃Q:Coefficient F (C.side b p),Q.Format 0 C.params R! ∧
      Q.remBound 0 R! (safety C b) (∑i,‖w i‖*r i) ∧ (F).coeffSize Q.x ≤ ∑i,‖w i‖*r i ∧
      credit C N p h (∑i,w i • f i) b live=Q.density 0 S! R!:=by
  classical
  rcases isEmpty_or_nonempty I with empty|has
  · letI:=empty
    let q:=(C.factory h N p).entries b (0:C.label h)
    have billed:=entryOk (C:=C) h N p b H start live (0:C.label h)
    refine ⟨stretch 0 q,stretch_format 0 billed.1,?_,?_,?_⟩
    · simpa using stretch_rem (0:ℂ) billed.2
    · change (F).coeffSize ((0:ℂ) • q.x)≤_
      simp
    · rw [IntrinsicProductLinearity.credit_sum C N p h b live w f cont]
      funext U
      rw [stretch_density]
      simp
  · letI:=has
    let q (i:I):=stretch (w i) (K i)
    let total:=Extra.Histories.merge (code I) q
    have admit(i:I):(q i).Format 0 C.params R!:=stretch_format _ (row i).1
    have charges(i:I):(q i).remBound 0 R! (safety C b) (‖w i‖*r i):=stretch_rem _ (row i).2.1
    have pos:0<safety C b:=Real.sqrt_pos.mpr (forcedPos C.path.levels b)
    refine ⟨total,merge_format _ _ admit,?_,?_,?_⟩
    · simpa only [tsum_fintype] using (merge_budget (code I) q pos charges Summable.of_finite).1
    · change (F).coeffSize (∑' i,(q i).x)≤_
      rw [tsum_fintype]
      apply (Size.finite F Finset.univ _).trans
      refine Finset.sum_le_sum fun i _=>?_
      change (F).coeffSize (w i • (K i).x)≤_
      rw [Size.smul]
      exact mul_le_mul_of_nonneg_left (row i).2.2.1 (norm_nonneg _)
    · rw [IntrinsicProductLinearity.credit_sum C N p h b live w f cont]
      simp_rw [(row _).2.2.2]
      funext V
      have cap:=(merge_density (code I) q pos (H.wilson.represents N p b live).good charges
        Summable.of_finite Summable.of_finite S! V).tsum_eq
      rw [tsum_fintype] at cap
      rw [Finset.sum_apply]
      exact (Finset.sum_congr rfl fun i _=>(stretch_density S! R! 0 (w i) (K i) V).symm).trans cap

end YM.Integration.WilsonMacroscopicRichPortfolioCapture
