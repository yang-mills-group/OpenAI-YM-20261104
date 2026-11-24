import YM.Gaps1020.Local.Wear
import YM.MergeProof.Bungalow

/-! The native incoming density of an arbitrary finite original regular
marked menu retains the complete scalar hard gas of its physical world. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedOrdinaryDensity
open Function Finset Lattice Wilson RG Marker MergeProof MergeProof.Accent Menu
open Extra.Histories Extra.Trajectories Push.GridApprox.Nil
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
  {Γ : Census V} (Y : Rep G n) (m : I→Menu.Hat Γ Y) (slot : I→ℕ)

theorem original {a b : ℝ} (law : Y.activities.Valid Y.p a b)
    (regular : ∀i,(m i).M.turn=.logKey (slot i)) (U : Config G n) :
    GapsLocal.Full.given m 0 U=(Y.eval U:ℂ) • Poly.pass (∑i,Menu.amount (m i) U) := by
  have reg (i : I) : Menu.odour (m i) U=Menu.amount (m i) U := by
    unfold Menu.odour prose
    rw [regular i,Menu.varnish]
  have hard (i : I) (p : Box n) : Menu.fragrance (m i) U p=0 := by
    unfold Menu.fragrance entry
    simp [regular i]
  have gas : Accent.field (fun p=>Accent.bar Y.activities Γ U p+∑i,Menu.fragrance (m i) U p)
        (RG.flags Y.p.threshold U)=Poly.bead Γ (Y.activities.gas Y.p U:ℂ) := by
    simp only [hard,Finset.sum_const_zero,add_zero]
    exact Accent.hawk Y.activities Y.p Γ law U
  have zero : Accent.Mach Γ 0=0 := by simp [Accent.Mach]
  unfold GapsLocal.Full.given
  rw [zero,Extra.Trajectories.pass_zero,one_mul,gas]
  simp_rw [reg]
  rw [mul_comm (Poly.pass _) (Poly.bead Γ _),Poly.product_bead,smul_smul,Rep.eval,Complex.ofReal_mul]

end YM.Integration.OriginalMarkedOrdinaryDensity
end
