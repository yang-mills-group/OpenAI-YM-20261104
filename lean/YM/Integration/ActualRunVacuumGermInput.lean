import YM.Integration.ActualRunVacuumNorm
import YM.Integration.ActualRunStrongIntake
import YM.Integration.ActualRunSpring

/-! The literal pre-reset density at the fixed requested norm, and the native
reset geometry supplied by the same Run. The output support is the already
chosen quarter of the initial support exponent. No new geometric payment,
new trajectory, or equality of beta parameters is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunVacuumGermInput
open Function Lattice Wilson RG
open PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection Quotes
open IterationFour.Vacuum YM.Integration.LocalComparison
open scoped BigOperators
variable {G : Gauge} {n : Side}

private lemma labels_eq (W : PathData G) (p q : BudgetPoint) (X : Listing G n)
    (hB : p.B = q.B) : PreReset.labels W p X = PreReset.labels W q X := by
  funext i
  rcases i with i | i
  · rfl
  rcases i with i | i
  · simp only [PreReset.labels, Sum.elim_inr, Sum.elim_inl, lowEntry, Low.home, hB]
  · rfl

/-- Every original activity and all rendered rows are preserved by this
literal budget update; the block-cover parameter fixes the low-row labels. -/
theorem append_budget_eq (S : List (Piece G n)) (W : PathData G) (c : Clip)
    (p q : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (β τ α : ℝ) (k : Piece G n → ℝ) (hB : p.B = q.B) :
    ({ PreReset.append S W c p X v β τ α k with p := q } : Rep G n) =
      PreReset.append S W c q X v β τ α k := by
  have hl := labels_eq W p q X hB
  simp only [PreReset.append, Render.append, PreReset.rep, PreReset.activities, hl]

/-- Full density equality includes every original forced predicate and value. -/
theorem append_eval_eq (S : List (Piece G n)) (W : PathData G) (c : Clip)
    (p q : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (β τ α : ℝ) (k : Piece G n → ℝ)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    (PreReset.append S W c p X v β τ α k).eval =
      (PreReset.append S W c q X v β τ α k).eval := by
  calc
    _ = ({ PreReset.append S W c p X v β τ α k with p := q } : Rep G n).eval :=
      ActualRunVacuumNorm.eval_same_threshold _ p q hT
    _ = _ := congrArg Rep.eval (append_budget_eq S W c p q X v β τ α k hB)

/-- The retained Spring supplies the original reset geometry at every stage. -/
theorem native_geometry (R : Run G) (m : ℕ) :
    WilsonStartup.Decent (R.family.path.levels.params m).clip
      (R.family.path.levels.budget m) ∧
    Geo.Width (R.family.path.levels.budget m)
      (R.family.path.levels.params m).clip (R.family.path.levels.params m).width := by
  let P := ActualRunSpring.selected R (m+1) 0 m (Nat.lt_succ_self m)
  have hp := (R.kit.machine.passes (Nat.lt_succ_self m) P.spring.knows).1
  exact ⟨hp.decent, hp.width⟩

/-- The already-selected fixed output support only decreases the native
support requirement. All other reset geometry is literally unchanged. -/
theorem output_geometry (R : Run G) {V : Type} [DecidableEq V] [Fintype V]
    (J : Global.Setup V) (A : Global.Admission R.family J)
    (hJ : J.outputSupport = ActualRunStrongIntake.outputSupport R) (m : ℕ) :
    WilsonStartup.Decent (R.family.path.levels.params m).clip (A.outputNorm m) ∧
    Geo.Width (A.outputNorm m) (R.family.path.levels.params m).clip
      (R.family.path.levels.params m).width := by
  obtain ⟨hc, he⟩ := native_geometry R m
  have hB := (A.output_norm m).block
  have hT := (A.output_norm m).threshold
  have hs : (A.outputNorm m).supportExponent ≤
      (R.family.path.levels.budget m).supportExponent := by
    rw [(A.output_norm m).reserve, hJ]
    exact (ActualRunStrongIntake.supports_le R m).2
  constructor
  · exact ⟨hc.direct, by simpa only [hB] using hc.radius,
      by simpa only [hB, hT] using hc.cut⟩
  · refine ⟨he.1, he.2.1, ?_⟩
    rw [hB]
    calc
      _ ≤ ((R.family.path.levels.budget m).supportExponent + 1) /
          (R.family.path.levels.budget m).B :=
        div_le_div_of_nonneg_right (by linarith only [hs]) (Nat.cast_nonneg _)
      _ ≤ _ := he.2.2

/-- No late period threshold is added: the original Run already has room. -/
theorem period_room (R : Run G) (m period : ℕ) :
    20 < (R.family.side m period).val :=
  Return.enough_room R.alloy.B m period

end YM.Integration.ActualRunVacuumGermInput
end
