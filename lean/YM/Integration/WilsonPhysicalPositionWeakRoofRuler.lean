import YM.Integration.WilsonPhysicalPositionFirstWeakClock

/-! Slow admission of arbitrarily late finite grade menus, with a single
ruler chosen before any physical position. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionWeakRoofRuler
open Filter Set
open scoped Classical Topology

def height (base onset:ℕ → ℝ) (x:ℝ) : ℝ :=
  ⨅ d:ℕ, base d + max 0 (x - onset d)

private theorem below (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) (x:ℝ) :
    BddBelow (Set.range (fun d=>b d+max 0 (x-t d))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨d,rfl⟩
  exact add_nonneg (positive d) (le_max_left ..)

theorem at_grade (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) (x:ℝ) (d:ℕ) :
    height b t x ≤ b d+max 0 (x-t d) :=
  ciInf_le (below b t positive x) d

theorem rate (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) {x y:ℝ} (xy:x≤y) :
    height b t x ≤ height b t y ∧ height b t y - height b t x ≤ y-x := by
  constructor
  · apply le_ciInf
    intro d
    exact (at_grade b t positive x d).trans
      (add_le_add_right (max_le_max le_rfl (sub_le_sub_right xy _)) _)
  · apply sub_le_iff_le_add.mpr
    rw [add_comm]
    apply sub_le_iff_le_add.mp
    apply le_ciInf
    intro d
    have growth : max 0 (y-t d) ≤ max 0 (x-t d)+(y-x) := by
      apply max_le
      · exact add_nonneg (le_max_left ..) (sub_nonneg.mpr xy)
      · linarith only [le_max_right 0 (x-t d)]
    linarith only [at_grade b t positive y d,growth]

theorem cofinal (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) (inc:Monotone b) (wait:Monotone t)
    (late:Tendsto b atTop atTop) : Tendsto (height b t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro target
  obtain ⟨D,hD⟩:=(late.eventually_ge_atTop target).exists
  filter_upwards [eventually_ge_atTop (t D+max 0 target)] with x hx
  apply le_ciInf
  intro d
  rcases le_total d D with earlier|later
  · linarith only [wait earlier,le_max_right 0 target,le_max_right 0 (x-t d),positive d,hx]
  · exact (hD.trans (inc later)).trans (le_add_of_nonneg_right (le_max_left ..))

theorem admissible (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) (inc:Monotone b)
    (late:Tendsto b atTop atTop) {x:ℝ} (ready:t 0 ≤ x) :
    ∃ d:ℕ,t d ≤ x ∧ b d ≤ height b t x ∧ height b t x ≤ b (d+1) := by
  obtain ⟨k,used⟩:=(late.eventually_ge_atTop (height b t x)).exists
  have existsGrade:∃ j:ℕ,height b t x ≤ b (j+1) := ⟨k,used.trans (inc (Nat.le_succ _))⟩
  let d:=Nat.find existsGrade
  have fits:height b t x ≤ b (d+1):=Nat.find_spec existsGrade
  refine ⟨d,?_,?_,fits⟩
  · rcases Nat.eq_zero_or_pos d with early|grown
    · simpa only [early] using ready
    · obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero grown.ne'
      have needed:b d < height b t x := by
        rw [hj]
        exact lt_of_not_ge (Nat.find_min existsGrade (show j<d by omega))
      by_contra! missed
      have cap:=at_grade b t positive x d
      rw [max_eq_left (sub_nonpos.mpr missed.le),add_zero] at cap
      exact needed.not_ge cap
  · rcases Nat.eq_zero_or_pos d with early|grown
    · rw [early]
      apply le_ciInf
      intro j
      exact (inc (Nat.zero_le j)).trans (le_add_of_nonneg_right (le_max_left ..))
    · obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero grown.ne'
      rw [hj]
      exact le_of_lt (lt_of_not_ge (Nat.find_min existsGrade (show j<d by omega)))

theorem capped (b t:ℕ → ℝ) (positive:∀ d,0 ≤ b d) {x:ℝ} (floor:b 0 ≤ t 0) (ready:t 0 ≤ x) :
    height b t x ≤ x := by
  have h:=at_grade b t positive x 0
  rw [max_eq_right (sub_nonneg.mpr ready)] at h
  linarith

end YM.Integration.WilsonPhysicalPositionWeakRoofRuler
end
