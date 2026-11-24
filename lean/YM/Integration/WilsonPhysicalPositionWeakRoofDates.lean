import YM.Integration.WilsonPhysicalPositionWeakRoofClock

/-! The grade and all of its delayed purchases are selected before the reporting radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionWeakRoofDates
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Next.Rank
open WilsonPhysicalPositionWeakRoofRuler WilsonPhysicalPositionWeakRoofClock
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem reserve (b x : ℕ → ℝ) (needs : ℕ → ℕ) :
    ∃ t : ℕ → ℝ, Monotone t ∧ b 0 ≤ t 0 ∧ ∀ d k, t d ≤ x k → needs d ≤ k := by
  let bill (d : ℕ) := max (b d) (1 + ∑ i ∈ Finset.range (needs d), max 0 (x i))
  let t : ℕ → ℝ := Nat.rec (bill 0) (fun d z => max z (bill (d+1)))
  have mt : Monotone t := monotone_nat_of_le_succ (fun d => le_max_left ..)
  have above (d : ℕ) : bill d ≤ t d := by
    cases d with
    | zero => exact le_rfl
    | succ d => exact le_max_right .. 
  refine ⟨t,mt,(le_max_left ..).trans (above 0),fun d k ready => ?_⟩
  by_contra! early
  have term : max 0 (x k) ≤ ∑ i ∈ Finset.range (needs d), max 0 (x i) :=
    Finset.single_le_sum (f := fun i => max 0 (x i)) (fun i _ => le_max_left ..) (Finset.mem_range.mpr early)
  have limit := (le_max_right (b d) (1 + ∑ i ∈ Finset.range (needs d), max 0 (x i))).trans
    ((above d).trans ready)
  linarith only [le_max_right 0 (x k),term,limit]

theorem original (R : Run G) (simple : G.Simple) (b : ℕ → ℝ) (mono : Monotone b)
    (pos : ∀ d, 0 ≤ b d) (late : Tendsto b atTop atTop) (needs : ℕ → ℕ) :
    ∃ (t : ℕ → ℝ) (d : ℕ → ℕ), Monotone t ∧ b 0 ≤ t 0 ∧ Tendsto d atTop atTop ∧
      Tendsto (dial R b t) atTop atTop ∧
      (∀ᶠ k in atTop, needs (d k) ≤ k ∧ b (d k) ≤ dial R b t k ∧
        dial R b t k ≤ b (d k + 1)) ∧
      ∀ᶠ k : ℕ in atTop, 2 * ruler R b t (k+1) ≤ ruler R b t k := by
  let x (k : ℕ) := Real.log (Real.log (R.family.path.levels.clock.hatBeta k))
  have hx : Tendsto x atTop atTop := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (Station.hat_rate R.family.path.levels simple))
  obtain ⟨t,mt,first,hfloor⟩ := reserve b x needs
  have hdial : Tendsto (dial R b t) atTop atTop :=
    (cofinal b t pos mono mt late).comp hx
  let d (k : ℕ) := if h : t 0 ≤ x k then
    Classical.choose (admissible b t pos mono late h) else 0
  have offered : ∀ᶠ k in atTop, needs (d k) ≤ k ∧ b (d k) ≤ dial R b t k ∧
      dial R b t k ≤ b (d k + 1) := by
    filter_upwards [hx.eventually_ge_atTop (t 0)] with k h
    have avail := Classical.choose_spec (admissible b t pos mono late h)
    dsimp only [d]
    rw [dif_pos h]
    exact ⟨hfloor _ _ avail.1,avail.2⟩
  refine ⟨t,d,mt,first,?_,hdial,offered,halves R simple b t pos first⟩
  apply tendsto_atTop.2
  intro D
  filter_upwards [offered, hdial.eventually_gt_atTop (b (D+1))] with k live past
  by_contra! small
  exact (not_le_of_gt past) (live.2.2.trans (mono (Nat.succ_le_succ small.le)))

end YM.Integration.WilsonPhysicalPositionWeakRoofDates
end
