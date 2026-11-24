import YM.Integration.WilsonIndependentCapturedRocket

/-! Propagate one signed discrepancy of the two complete occupied words
on their shared deposited vacuum. Each word keeps its original valence
and its own incoming scalar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedContrast
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Step RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Profiles RegulatorIR.Sources
open RegulatorIR.Cluster RegulatorIR.Uniform Lattice RG
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side}
variable (S : Heir n G) (T : S.Accounts) {p k m h a : ℕ} {L : Meter W}
variable (H : Milieu S T k p L)
include H

theorem inventory (Z : T.Report h) (start : ∀ w, Bill (Z.main (Page.opening M w)) p) :
    ∀ j : Page M, Bill (Z.main j) p := by
  apply Page.proves (g:=fun j => Bill (Z.main j) p) start
  intro f prior
  rw [← Z.step_m f]
  exact estimateM H f prior

theorem balance (incoming : T.Report m) (issued : T.Report h) (error : T.Report a)
    (old : ∀ w, Bill (incoming.main (Page.opening M w)) p)
    (fresh : ∀ w, Bill (issued.main (Page.opening M w)) p)
    (joined : ∀ w e, e ≤ p → incoming.main (Page.opening M w) e -
      issued.main (Page.opening M w) e = error.main (Page.opening M w) e) :
    ∀ j : Page M, ∀ e, e ≤ p → incoming.main j e - issued.main j e = error.main j e := by
  apply Page.proves (g:=fun j => ∀ e, e ≤ p → incoming.main j e - issued.main j e = error.main j e) joined
  intro f landed e he
  let step := S.frames f
  let quiet := T.bulk f.prev
  let cap := max (max m h) a
  have vac := step.joint_vac_shape (T.cap_b H.core.grade f.prev) (H.core.grade f)
  have R := WilsonIndependentCapturedValence.cover step quiet (incoming.main f.prev) vac
    (incoming.cap_b H.core.grade f.prev) (show m ≤ cap from (le_max_left m h).trans (le_max_left ..))
  have Z := WilsonIndependentCapturedValence.cover step quiet (issued.main f.prev) vac
    (issued.cap_b H.core.grade f.prev) (show h ≤ cap from (le_max_right m h).trans (le_max_left ..))
  have E := WilsonIndependentCapturedValence.cover step quiet (error.main f.prev) vac
    (error.cap_b H.core.grade f.prev) (show a ≤ cap from le_max_right ..)
  have subtract := Cluster.each_minus (A:=fun j => incoming.main j.prev) (B:=fun j => issued.main j.prev)
    S.lifts (Vac S T) (H.fund (b:=k) le_rfl) (H.solid (b:=k) le_rfl) (n:=cap) f
    (inventory S T H incoming old f.prev) (inventory S T H issued fresh f.prev) he
  rw [← incoming.step_m f, ← issued.step_m f, ← error.step_m f]
  change step.each m quiet _ e - step.each h quiet _ e = step.each a quiet _ e
  rw [R,Z,E]
  exact subtract.symm.trans (survivesP step quiet landed he)

end YM.Integration.WilsonIndependentCapturedContrast
