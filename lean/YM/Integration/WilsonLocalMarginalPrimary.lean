import YM.Integration.WilsonCoherentMeasuredStencil

/-! The full registered primary, including its complement to the physical
healthy chart, is an admissible correlated test under the true Haar prior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalMarginalPrimary
open Function Set Finset MeasureTheory Lattice RG Wilson PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem slot {n:Side} (d:ℕ) (o:Site n) (θ:ℝ) (y:R.family.label d) :
    let F:=Push.Local.primary (R.family.localSection d) o θ y
    Measurable F ∧ ∃c:ℝ,0≤c ∧ ∀U,‖F U‖≤c := by
  intro F
  let S:=R.family.localSection d
  let x:=(R.family.labels.level d).core y
  let h:=Push.Local.presented S o θ x
  have cont:Continuous h:=S.continuous_places _ _
  obtain ⟨c,b⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
  change Measurable (fun u=>y 0+masked θ (S.footprint o) h u) ∧ _
  refine ⟨measurable_const.add (masked_measurable _ _ _ cont.measurable),‖y 0‖+max 0 c,
    add_nonneg (norm_nonneg _) (le_max_left 0 c),fun U=>?_⟩
  apply (norm_add_le (y 0) (masked θ (S.footprint o) h U)).trans
  apply add_le_add_right
  by_cases live:Healthy θ (S.footprint o) U
  · rw [masked_eq _ _ _ _ live];exact (b U (mem_univ U)).trans (le_max_right _ _)
  · rw [masked_ne _ _ _ _ live,norm_zero];exact le_max_left _ _

def held {n:Side} (d:I→ℕ) (o:I→Site n) (θ:ℝ) (y:∀i,R.family.label (d i)) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (U:Config G n) :=
  χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)

theorem bounded {n:Side} (d:I→ℕ) (o:I→Site n) (θ:ℝ) (y:∀i,R.family.label (d i)) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) :
    Envelope (held R d o θ y c χ) := by
  let f (i:I):=Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i)
  have paid i:=slot R (d i) (o i) θ (y i)
  choose B pos prices using fun i=>(paid i).2
  refine ⟨χ.continuous.measurable.comp ((Finset.measurable_prod _ fun i _=>(paid i).1).const_mul c),
    ‖χ‖*(‖c‖*∏i,B i),fun U=>?_⟩
  refine (χ.le_opNorm (c*∏i,f i U)).trans ?_
  rw [norm_mul,norm_prod]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (prod_le_prod (fun i _=>norm_nonneg (f i U)) (fun i _=>prices i U)) (norm_nonneg _)) (norm_nonneg _)

end YM.Integration.WilsonLocalMarginalPrimary
