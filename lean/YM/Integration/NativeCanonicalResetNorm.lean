import YM.IterationFour.Vacuum.Reclose
import YM.IterationFour.Vacuum.Render

/-! The canonical reset keeps its complete merger when only price coordinates
change. A Rep stores its BudgetPoint, so the exact record identity explicitly
updates that field. No Rates, new selection, or bound is inferred here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeCanonicalResetNorm
open Function Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Quotes Averaging
open IterationFour.Vacuum Progress.DirectedRecipe Ovens
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

private theorem low_entry_eq (W : PathData G) (p q : BudgetPoint)
    (hB : p.B = q.B) (i : Seat n × Low) :
    lowEntry G W p i = lowEntry G W q i := by
  apply reg_ext
  · rfl
  · change i.1.spread (i.2.home W p 0) = i.1.spread (i.2.home W q 0)
    simp only [Low.home, hB]

private theorem shelves_eq (W : PathData G) (p q : BudgetPoint)
    (hB : p.B = q.B) (X : Listing G n) :
    shelves X W p = shelves X W q := by
  have hi : incoming X W p = incoming X W q := by
    funext i
    rcases i with i | i
    · rfl
    rcases i with i | i
    · exact low_entry_eq W p q hB i
    · rfl
  have hs : soft X W p = soft X W q := by
    funext i
    rcases i with i | i
    · rfl
    exact congrArg RegularAddress.support (low_entry_eq W p q hB i)
  simp only [shelves, hi, hs]

private theorem loses_eq (W : PathData G) (c : Clip) (p q : BudgetPoint)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (X : Listing G n) (v : Collection.Source G n) (alpha Delta : ℝ) :
    loses X W c p v alpha Delta = loses X W c q v alpha Delta := by
  funext i U
  rcases i with i | i
  · change Residual.fault (X.reg i) (v.logRead i) p.threshold U =
      Residual.fault (X.reg i) (v.logRead i) q.threshold U
    rw [hT]
  change Low.loan W c i.2 0 p (factor * alpha) (factor * Delta) (i.1.view U) =
    Low.loan W c i.2 0 q (factor * alpha) (factor * Delta) (i.1.view U)
  simp only [Low.loan, Low.home, Low.live, hB, hT]

private theorem reserve_eq (W : PathData G) (c : Clip) (p q : BudgetPoint)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (X : Listing G n) (v : Collection.Source G n) (alpha Delta : ℝ) :
    Reset.reserve W c p X v alpha Delta = Reset.reserve W c q X v alpha Delta := by
  simp only [Reset.reserve, Collection.fill, loses_eq W c p q hB hT X v alpha Delta]

private theorem fused_eq {Y : Pipes G n} (F : ℕ ≃ Y.Pellet)
    (p q : BudgetPoint) (hT : p.threshold = q.threshold) (d : Tap G n) :
    Pipes.fused F p d = Pipes.fused F q d := by
  have ha : Pipes.addr F p = Pipes.addr F q := by
    have hc : Pipes.condition F p = Pipes.condition F q := by
      funext i U
      simp only [Pipes.condition, hT]
    funext i
    simp only [Pipes.addr, hc]
  have hk : Pipes.solid F p d = Pipes.solid F q d := by
    funext i U
    simp only [Pipes.solid, ha, hT]
  simp only [Pipes.fused, ha, hk]

/-- Exact record identity: all fields except the displayed stored norm are
unchanged. The fixed drawer and folio keep every merger occurrence. -/
theorem after_budget_eq (W : PathData G) (c : Clip) (p q : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (beta tau alpha : ℝ)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    ({Reset.after W c p X v beta tau alpha with p := q} : Rep G n) =
      Reset.after W c q X v beta tau alpha := by
  simp only [Reset.after, finish, shelves_eq W p q hB X,
    reserve_eq W c p q hB hT X v alpha, fused_eq (folio G n) p q hT]

/-- Appending the same complete model list commutes with the same norm update. -/
theorem append_budget_eq (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ)
    (k : Piece G n → ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    ({Render.append S (Reset.after W c p X v beta tau alpha) k with p := q} :
      Rep G n) =
      Render.append S (Reset.after W c q X v beta tau alpha) k := by
  exact congrArg (fun Q : Rep G n => Render.append S Q k)
    (after_budget_eq W c p q X v beta tau alpha hB hT)

/-- The actual functions and their complete regular/forced labels coincide. -/
theorem append_activities_eq (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ)
    (k : Piece G n → ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold) :
    (Render.append S (Reset.after W c p X v beta tau alpha) k).activities =
      (Render.append S (Reset.after W c q X v beta tau alpha) k).activities := by
  have h := congrArg (fun Q : Rep G n => Q.activities)
    (append_budget_eq S W c p q X v beta tau alpha k hB hT)
  exact h

private theorem exponent_rebudget (Q : Rep G n) (q : BudgetPoint)
    (hT : Q.p.threshold = q.threshold) (U : Config G n) :
    Q.exponent U = ({Q with p := q} : Rep G n).exponent U := by
  simp only [Rep.exponent, PathData.inChannels, PathData.principal,
    PathData.baseTerm, PathData.atomSeries, Atom.placed,
    Activities.additive, Activities.regularOccurrence, hT]

private theorem gas_eq (A : Activities G n) (p q : BudgetPoint)
    (hT : p.threshold = q.threshold) (U : Config G n) :
    A.gas p U = A.gas q U := by
  simp only [Activities.gas, Activities.gasOccurrence, Activities.admissible, hT]
  apply tsum_congr
  intro b
  split_ifs <;> rfl

/-- The complete exponent agrees, including its original centered scalar. -/
theorem append_exponent_eq (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ)
    (k : Piece G n → ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (U : Config G n) :
    (Render.append S (Reset.after W c p X v beta tau alpha) k).exponent U =
      (Render.append S (Reset.after W c q X v beta tau alpha) k).exponent U := by
  exact (exponent_rebudget
    (Render.append S (Reset.after W c p X v beta tau alpha) k) q hT U).trans
    (congrArg (fun Q : Rep G n => Q.exponent U)
      (append_budget_eq S W c p q X v beta tau alpha k hB hT))

/-- Full physical equality includes the actual gas, also when it vanishes. -/
theorem append_eval_eq (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ)
    (k : Piece G n → ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (U : Config G n) :
    (Render.append S (Reset.after W c p X v beta tau alpha) k).eval U =
      (Render.append S (Reset.after W c q X v beta tau alpha) k).eval U := by
  apply congrArg₂ (fun x y : ℝ => Real.exp x * y)
    (append_exponent_eq S W c p q X v beta tau alpha k hB hT U)
  exact (congrArg (fun A : Activities G n => A.gas p U)
    (append_activities_eq S W c p q X v beta tau alpha k hB hT)).trans
    (gas_eq (Render.append S (Reset.after W c q X v beta tau alpha) k).activities
      p q hT U)

/-- A bound at any supplied norm transfers literally; it is not inferred from
a bound at a weaker norm. -/
theorem append_kbound_iff (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ)
    (k : Piece G n → ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (r : BudgetPoint) (w : ℝ) :
    (Render.append S (Reset.after W c p X v beta tau alpha) k).activities.KBound r w ↔
      (Render.append S (Reset.after W c q X v beta tau alpha) k).activities.KBound r w := by
  rw [append_activities_eq S W c p q X v beta tau alpha k hB hT]

/-- The reset coefficient and the full flat-log centering are unchanged. -/
theorem append_parameters (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (beta tau alpha : ℝ) (k : Piece G n → ℝ) :
    (Render.append S (Reset.after W c p X v beta tau alpha) k).beta =
        beta + alpha + delta (X.read v) ∧
      (Render.append S (Reset.after W c p X v beta tau alpha) k).v = vac v tau := by
  exact ⟨rfl, rfl⟩

end YM.Integration.NativeCanonicalResetNorm
end
