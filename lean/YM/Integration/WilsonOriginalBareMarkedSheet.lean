import YM.Integration.WilsonRootedKioskSlipCharge
import YM.QuadraticLocal.Shelter.Shadows

/-! The signed failed selector which restores a bare family on the measured inlet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBareMarkedSheet
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal
open WilsonRootedKioskOccupiedSlip
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{p:BudgetPoint}{o:V → Site n}{R:Census V}

theorem shaded (L:Lamps T I G p o R) (t:T)(U:Config G n) : bare L.shade t U = -bare L t U := by
  have sends (s:R.Mode) (z:ℂ) : Poly.send s (-z) = -Poly.send s z := by
    ext m
    simp only [Poly.part_send,Poly.part_neg]
    split <;> simp
  unfold WilsonRootedKioskOccupiedSlip.bare
  simp only [Lamps.shade,Pi.neg_apply,sends,tsum_neg]

theorem restore [Fintype I] (L:Lamps T I G p o R) (t:T)(U:Config G n) :
    bare L t U=L.log t U+(sheet L.shade).log t U := by
  have h:=split L.shade t U
  rw [Lamps.shade_log,shaded] at h
  linear_combination (norm:=abel) h

theorem charged (L:Lamps T I G p o R) {w:V → ℝ}{h a v:ℝ}{B:ℕ}
    (pos:∀j,0<w j)(one:1≤h)(paid:Gross L w B a v) :
    (sheet L.shade).Budget (fun j=>w j/h) B a (h⁻¹*v) := by
  apply WilsonRootedKioskSlipCharge.cost _ pos one
  obtain ⟨f,hf,all,hit⟩:=paid.before
  exact ⟨f,hf,fun i t U=>by simpa only [Lamps.shade,Pi.neg_apply,norm_neg] using all i t U,hit⟩

end YM.Integration.WilsonOriginalBareMarkedSheet
