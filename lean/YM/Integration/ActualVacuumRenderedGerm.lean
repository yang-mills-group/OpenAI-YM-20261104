import YM.Integration.ActualRunVacuumGermInput
import YM.Integration.VacuumGermReset
import YM.Integration.KineticGerm

/-! Functional re-expression of the exact selected vacuum on kinetic germs.
The full-density equality is supplied by the same produced carrier; no listing
identity or equality of its beta to the actual trajectory beta is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualVacuumRenderedGerm
open Function Filter Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Geo
open IterationFour.Vacuum LocalComparison
open scoped Topology
variable {G : Gauge} {n : Side} {W : PathData G} {c : Clip}
    {p q : BudgetPoint} {X : Listing G n} {v : Collection.Source G n}
    {σ C Λ H w : ℝ} {P : Rep G n}

/-- Equality on the original good configurations, preserving all scalar terms. -/
theorem good_eq (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : WilsonStartup.Decent c p) (hw : Width p c σ)
    (S : List (Piece G n)) (k : Piece G n → ℝ) (hS : Render.permits S p)
    (β τ α : ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (hFull : (PreReset.append S W c q X v β τ α k).eval = P.eval)
    (U : Config G n) (hU : flags p.threshold U = ∅) :
    (Render.append S (VacuumGermReset.shell W c p X v β τ α) k).eval U = P.eval U := by
  have hE := ActualRunVacuumGermInput.append_eval_eq S W c p q X v β τ α k hB hT
  exact (VacuumGermReset.rendered_good_eval g hn h hv hc hw β τ α S k hS U hU).trans
    (congrFun (hE.trans hFull) U)

/-- Each native row-wave has the same local density; the radius may depend on it. -/
theorem rendered_germ (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : WilsonStartup.Decent c p) (hw : Width p c σ)
    (S : List (Piece G n)) (k : Piece G n → ℝ) (hS : Render.permits S p)
    (β τ α : ℝ) (hB : p.B = q.B) (hT : p.threshold = q.threshold)
    (hFull : (PreReset.append S W c q X v β τ α k).eval = P.eval) :
    ∀ (a : G.Color), ‖a‖ = 1 → ∀ b : Bool, ∀ᶠ t : ℝ in 𝓝 0,
      (Render.append S (VacuumGermReset.shell W c p X v β τ α) k).eval
        (line (YM.Pert.Kinetic.rowWave a b) t) =
      P.eval (line (YM.Pert.Kinetic.rowWave a b) t) := by
  intro a _ha b
  filter_upwards [YM.Pert.Kinetic.rays_free p.threshold p.threshold_pos
    (YM.Pert.Kinetic.rowWave a b)] with t ht
  exact good_eq g hn h hv hc hw S k hS β τ α hB hT hFull _ ht

end YM.Integration.ActualVacuumRenderedGerm
end
