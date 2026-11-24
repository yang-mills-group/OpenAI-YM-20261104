import YM.Integration.WilsonOriginalOPEPageMenu
import YM.Gaps1020.Local.Wear

/-! Repeated regular insertions occupy the manuscript's complete heap. Its
physical expense agrees with every original ordinary and forced mark at every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOPECompleteExpense
open Function Finset Lattice Wilson RG Marker MergeProof MergeProof.Accent
open Extra.Trajectories Overlay.GapsLocal
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} {R P : Rep G f} {I V : Type}
    [Fintype I] [DecidableEq V] [Fintype V] {Γ : Census V} (a : I → Menu.Hat Γ R)

/-- The complete finite exponential obtained from the charged ordinary leaves,
with the gas on its original countably many labels, at every configuration. -/
theorem spent (S : StepData c f) (w : V → ℝ) (hw : ∀v,0<w v)
    {σ α b d e : ℝ} (law : R.Lawful σ α b d e) :
    GapsLocal.Full.given a 0 = Menu.Expense (Menu.heap a) w S := by
  rw [GapsLocal.Full.fragrant a (0 : V→ℂ) S law hw]
  funext U
  change Poly.pass (Accent.Mach Γ 0) * _ = _
  have zero : Accent.Mach Γ 0 = 0 := by simp [Accent.Mach,Poly.send_zero]
  rw [zero, Extra.Trajectories.pass_zero,one_mul]
  rfl

/-- The stored native fine endpoint identifies the entire source menu. -/
theorem transported (eq : R=P) (o : V→Site f) (w : V→ℝ) {D : ℝ}
    (offer : Menu.Offer o a w R.p.B (R.p.supportExponent-4) D) :
    ∃ b : I→Menu.Hat Γ P, GapsLocal.Full.given a 0=GapsLocal.Full.given b 0 ∧
      Menu.Offer o b w P.p.B (P.p.supportExponent-4) D := by
  subst P
  exact ⟨a,rfl,offer⟩

end YM.Integration.WilsonOriginalOPECompleteExpense
end
