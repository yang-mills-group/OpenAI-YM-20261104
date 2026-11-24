import YM.Source.Preservation
import YM.Push.LOCAL_SPLITTING.Calculus

/-! The actual regular part of a measured coefficient is bounded at *every*
field; this does not require pointwise control of its signed forced fraction.
It agrees with the complete physical observation on the genuine clean chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.RegularProjection
open Function Finset Lattice Wilson RG Source Labels MeasureTheory
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} (Q : Coefficient F n)

def soft : Coefficient F n := {Q with forced := fun _ _ => 0}
variable (o : Site n) (Y : Rep G n) (A : Hol G) (S : SectionData F)

theorem format (h : Q.Format o A Y) : (soft Q).Format o A Y := by
  refine ⟨h.smooth,h.origin,h.identity_null,h.projects,?_,?_,?_,?_,?_⟩
  · intro i U nz; exact False.elim (nz rfl)
  · intro i nz; exact False.elim (nz rfl)
  · exact fun _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ => measurable_const

theorem bill {κ fee : ℝ} (paid : Q.remBound o Y κ fee) : (soft Q).remBound o Y κ fee := by
  obtain ⟨a,b,ha,hb,hfee,hκ,hreg,k,hf,hcost⟩ := paid
  refine ⟨a,b,ha,hb,hfee,hκ,hreg,k,hf,fun i => ⟨(hcost i).1,fun U => ?_⟩⟩
  simpa [soft] using (hcost i).1

theorem zero (b : Finset ℕ) (W : Config G n) : (soft Q).marked Y b W=0 := by
  classical
  unfold Coefficient.marked
  split_ifs <;> simp [soft]

theorem density (W : Config G n) : (soft Q).density o S Y W = (Y.eval W : ℂ)* Q.exponentialEntry o S Y W := by
  unfold Coefficient.density
  simp_rw [zero]
  simp only [tsum_zero,mul_zero,add_zero]
  rfl

theorem clear (h : Q.Format o A Y) (W : Config G n) (clean : flags Y.p.threshold W = ∅) :
    ∀ b, Q.marked Y b W = 0 := by
  have vacant (i : ℕ) : Q.forced i W=0 := by
    by_contra nz
    have fixed := (h.forcing i W nz).1
    rw [clean,Finset.inter_empty] at fixed
    exact (Y.activities.forced i).inventory_ne.ne_empty fixed.symm
  intro b
  unfold Coefficient.marked
  split_ifs <;> simp [vacant]

theorem clean_field (h : Q.Format o A Y) (W : Config G n) (clean : flags Y.p.threshold W=∅)
    (pos : 0 < Y.eval W) : Q.density o S Y W/(Y.eval W : ℂ)=Q.exponentialEntry o S Y W := by
  have nz : (Y.eval W : ℂ)≠0 := by exact_mod_cast pos.ne'
  unfold Coefficient.density; simp_rw [clear Q o Y A h W clean]
  simp [nz]

theorem ordinary {ν fee : ℝ} (paid : Q.remBound o Y ν fee) (W : Config G n) :
    ‖∑' i,Q.maskedTerm Y i W‖ ≤ fee := by
  obtain ⟨a,b,_,hb,cost,_,⟨e,raw,jets⟩,_⟩ := paid
  have row (i : ℕ) : ‖Q.maskedTerm Y i W‖ ≤ Y.p.mass (Q.support i) (e i) := by
    apply le_trans (b:=e i) _ (Y.p.loMass _ _ (jets i).1)
    by_cases yes : Healthy Y.p.threshold (Q.support i) W
    · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ yes]
      exact (jets i).2 W yes [] (Nat.zero_le _) (by simp)
    · rw [Coefficient.maskedTerm,masked_ne _ _ _ _ yes,norm_zero]
      exact (jets i).1
  have normed := raw.2.1.of_nonneg_of_le (fun i => norm_nonneg (Q.maskedTerm Y i W)) row
  exact ((norm_tsum_le_tsum_norm normed).trans ((normed.tsum_le_tsum row raw.2.1).trans raw.2.2)).trans
    (by linarith only [hb,cost])

theorem bounded {ν fee primary : ℝ} (paid : Q.remBound o Y ν fee)
    (jet : Y.p.supBounds o (S.footprint o) (S.places (F.scaled Y.p.threshold⁻¹ (F.core Q.x)) o) primary)
    (W : Config G n) : ‖Q.exponentialEntry o S Y W‖ ≤ ‖Q.x 0‖+primary+fee := by
  have head : ‖masked Y.p.threshold (S.footprint o)
      (S.places (F.scaled Y.p.threshold⁻¹ (F.core Q.x)) o) W‖ ≤ primary := by
    by_cases yes : Healthy Y.p.threshold (S.footprint o) W
    · rw [masked_eq _ _ _ _ yes];exact jet.2 W yes [] (Nat.zero_le _) (by simp)
    · rw [masked_ne _ _ _ _ yes,norm_zero];exact jet.1
  exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add le_rfl head)) (ordinary Q o Y paid W))

end YM.Integration.WilsonPhysicalMarkedDefect.RegularProjection
