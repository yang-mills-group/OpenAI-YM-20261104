import YM.Integration.WilsonIndependentFreshReplica

/-! The authentic evolved vacuum on every growing copy supplies the finite
Ward identity for a word born at capture, along its entire remaining history. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace YM.Integration.WilsonIndependentFreshCopyRange
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Halo.Sight
open RegulatorIR.Uniform RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ward
open WilsonIndependentFreshReplica
open scoped Topology ContDiff
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}
  (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p b m s : ℕ} (B : S.Primitive L p b)
  (Z : (E.part S T B).Report m) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w))) (w : W)

include stamp in
theorem all :
    ∃ measured : Side → ℝ → ℝ, ∀ j : Page (copy E w).spans,
      Nonempty (RangeR G (big w n ((copy E w).page j)) ((grove H w large).spot ((copy E w).page j))
        (measured j.bindW) s m ((tele H T w).orb ((copy E w).page j))
          ((report H T quiet large E B Z w).point j)) := by
  let K := grove H w large
  let V := tele H T w
  let vac : V.Report 0 := declaring V (fun _ => 0) (fun _ _ _ h => (h rfl).elim)
  let oldWord : Side → Portrait G := 0
  have oldReceipt (z : Side) : BasisT 0 0 (oldWord z) (vac.main (Page.opening (extent M w) z)) :=
    WilsonIndependentFreshQuietReel.priorZero G
  exact WilsonIndependentFreshWardHistory.dated _ V K.docket vac _
    (hinted K V vac (knows H T w large quiet) oldWord oldReceipt) (copy E w)
    (retained K V (copy E w)) (fun _ => rfl) (report H T quiet large E B Z w)
    (fun z => convey (root (n := n) E w z) (film w)) (origin H T quiet large E B Z w film stamp)

include stamp in
theorem observed (j : Page (copy E w).spans)
    (x y : ℝ → Horizon G (big w n ((copy E w).page j)))
    (hx : ContDiffAt ℝ ∞ x 0) (hy : ContDiffAt ℝ ∞ y 0) (equiv : reel_prop x y) :
    reel ((report H T quiet large E B Z w).point j) m x =
      reel ((report H T quiet large E B Z w).point j) m y := by
  obtain ⟨_,range⟩ := all H T quiet large E B Z film stamp w
  obtain ⟨r⟩ := range j
  exact RegulatorIR.Ward.RangeR.stamps r hx hy equiv

end YM.Integration.WilsonIndependentFreshCopyRange
