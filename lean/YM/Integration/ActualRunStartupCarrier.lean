import YM.FullVolume.Stage.Crests
import YM.Planned.RECIPE_STARTUP_PORT.Layout
import YM.Progress.DIRECTED_RECIPE.Batch

/-! The actual ultraviolet representative is the Campaign's retained startup
construction. Changing only norm coordinates keeps its complete regular and
forced rows when the block size and flag threshold agree. No bound or
replacement Run is inferred from an equality of evaluations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStartupCarrier
open Lattice Wilson RG Ovens
open WilsonStartup Progress.DirectedRecipe
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Muse
open scoped Classical

variable {G : Gauge} {n : Side}

/-- The fixed drawer and complete merger depend on the flag threshold. -/
theorem finish_activities_eq (W : PathData G) (c : Clip)
    (p q : BudgetPoint) (X : Pipes G n) (d : Tap G n) (beta v : ℝ)
    (hT : p.threshold = q.threshold) :
    (finish W c p X d beta v).activities =
      (finish W c q X d beta v).activities := by
  let F := folio G n
  have ha : Pipes.addr F p = Pipes.addr F q := by
    have hc : Pipes.condition F p = Pipes.condition F q := by
      funext i U
      simp only [Pipes.condition, hT]
    funext i
    simp only [Pipes.addr, hc]
  have hk : Pipes.solid F p (Rack.widen X d) =
      Pipes.solid F q (Rack.widen X d) := by
    funext i U
    simp only [Pipes.solid, ha, hT]
  change Pipes.fused F p (Rack.widen X d) = Pipes.fused F q (Rack.widen X d)
  simp only [Pipes.fused, ha, hk]

/-- Every original startup function is identical at equal block size and
threshold, including the nonzero forced bad-field terms. -/
theorem payload_eq (c : Clip) (p q : BudgetPoint) (beta : ℝ)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    Start.payload c p G n beta = Start.payload c q G n beta := by
  have hpad : pad p (n := n) = pad q := by
    funext x
    simp only [pad, hB]
  have hp : Start.paid c p (G := G) (n := n) = Start.paid c q := by
    funext i beta U
    simp only [Start.paid, Start.admission, Start.lives,
      region, hpad, charge, Key.owed, due, hB, hT]
  simp only [Start.payload, hp]

/-- Repricing the literal startup payload keeps all final labelled rows. -/
theorem startup_activities_eq (W : PathData G) (c : Clip)
    (p q : BudgetPoint) (beta v : ℝ)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    (finish W c p (Start.dictionary G n) (Start.payload c p G n beta)
      beta v).activities =
    (finish W c q (Start.dictionary G n) (Start.payload c q G n beta)
      beta v).activities := by
  rw [payload_eq c p q beta hB hT]
  exact finish_activities_eq W c p q (Start.dictionary G n)
    (Start.payload c q G n beta) beta v hT

/-- This is the whole representative retained by the same Campaign. -/
theorem top (R : Run G) (T : Campaign R) (N period : ℕ) :
    R.family.path.rep N period N =
      PhysicalNext.Repeat.Tent.launch (A := R.alloy) N period
        (R.family.path.rep N period N).beta := by
  exact (T.center N period).startStory T.gains

/-- The exact original top carrier has the requested-norm startup rows.
Its stored norm and its physical Run remain the original ones. -/
theorem top_activities_eq (R : Run G) (T : Campaign R) (N period : ℕ)
    (q : BudgetPoint)
    (hB : (R.family.path.levels.budget N).B = q.B)
    (hT : (R.family.path.levels.budget N).threshold = q.threshold) :
    (R.family.path.rep N period N).activities =
      (finish (R.alloy.B.kin.path N N) (R.family.path.levels.params N).clip
        q (Start.dictionary G (R.family.side N period))
        (Start.payload (R.family.path.levels.params N).clip q G
          (R.family.side N period) (R.family.path.rep N period N).beta)
        (R.family.path.rep N period N).beta 0).activities := by
  calc
    _ = (PhysicalNext.Repeat.Tent.launch (A := R.alloy) N period
        (R.family.path.rep N period N).beta).activities :=
      congrArg Rep.activities (top R T N period)
    _ = _ := startup_activities_eq (R.alloy.B.kin.path N N)
      (R.family.path.levels.params N).clip (R.family.path.levels.budget N) q
      (R.family.path.rep N period N).beta 0 hB hT

end YM.Integration.ActualRunStartupCarrier
end
