import YM.Integration.WilsonIndependentFreshWardHistory

/-! The newly marked finite Wilson numerator obeys the full nonlinear Ward
identity at each true retained date. Its final thermal series is the finite
volume Gaussian integral with the corresponding Haar terms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace YM.Integration.WilsonIndependentFreshReel
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Uniform
open RegulatorIR.StopB RegulatorIR.Ward PertExtension Series.Tested PowerSeries
open scoped Topology ContDiff
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side}
  {S : Heir n G} (H : Reel S) (T : S.Accounts) (quiet : H.Follows T)
  {m₀ s₀ : ℕ} (old : T.Report m₀) (top : W → Portrait G)
  (paid : ∀ w, BasisT m₀ s₀ (top w) (old.main (Page.opening M w)))
  (E : Era M) {L : Meter W} {p b m s : ℕ} (B : S.Primitive L p b)
  (Z : (E.part S T B).Report m) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))

def margins : Margins (fun j => Book G (n (E.page j))) where
  endK w := H.vapors (E.page (Page.finallyW E.spans w))
  haar w := charter G (n (E.page (Page.finallyW E.spans w)))

include quiet paid stamp in
theorem issued : ∃ measured : W → ℝ → ℝ,
    (∀ j : Page E.spans, Nonempty (RangeR G (n (E.page j)) (H.spot (E.page j))
      (measured j.bindW) s m (T.orb (E.page j)) (Z.point j))) ∧
    (∀ (j : Page E.spans) (x y : ℝ → Horizon G (n (E.page j))),
      ContDiffAt ℝ ∞ x 0 → ContDiffAt ℝ ∞ y 0 → reel_prop x y →
      reel (Z.point j) m x = reel (Z.point j) m y) ∧
    ∀ w, Aspiration (measured w) (fun i => coeff i (PowerSeries.X ^ s *
      PowerSeries.mk ((E.expanse S).vista (E.part S T B) Z (margins H E) w))) := by
  obtain ⟨g,registered⟩ := WilsonIndependentFreshWardHistory.original S T H.docket old
    (fun w => vital (TopF n w) (top w)) (hinted H T old quiet top paid) E B Z film stamp
  refine ⟨g,registered,?_,?_⟩
  · intro j x y hx hy equiv
    obtain ⟨r⟩ := registered j
    exact RegulatorIR.Ward.RangeR.stamps r hx hy equiv
  · intro w
    let j := E.page (Page.finallyW E.spans w)
    obtain ⟨r⟩ := registered (Page.finallyW E.spans w)
    obtain ⟨last⟩ := lens (H.suited j).1 (H.suited j).2 (H.even j)
    exact Binding.RangeR.tongue r last (H.even j)

end YM.Integration.WilsonIndependentFreshReel
