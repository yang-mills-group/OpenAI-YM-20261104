import YM.Integration.WilsonOriginalPrimerReceipts
import YM.Integration.WilsonOlderFreshConnectedAssembly

/-! Evaluation of the independently registered sparse coefficients at the
same finite group links as the submitted curvature lamp. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathJet
open Function Finset Filter Lattice RG Wilson Stationary QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Primitives.TwoWave PertExtension.Series PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical ContDiff
variable {U:Type}[Fintype U]

def diagonal (cap:ℕ)(T:Gen ℝ U)(a:Lawn U):ℝ:=
  ∑q∈range (cap+1),MvPolynomial.eval a (paint q (T q))

theorem sprig_read (f:Lawn U→ℝ)(r k cap:ℕ)(within:r+k≤cap)(a:Lawn U):
    diagonal cap (sprig f r k) a=Radial.jet f (r+k) a:=by
  classical
  unfold diagonal sprig
  rw [sum_eq_single (r+k),shine_lit]
  · simpa only [jet_apply,Radial.jet,smul_eq_mul] using (rayon f (r+k) a)
  · intro j _ diff
    rw [shine_dark (Ne.symm diff),map_zero,map_zero]
  · intro absent
    exact (absent (mem_range.mpr (Nat.lt_succ_of_le within))).elim

variable {G:Gauge}{n:Side}
theorem atom (p:Lantern G Unit)(x:Site n)(l e cap:ℕ)(within:p.r+(e-l)≤cap)(a:Link G n):
    WilsonOriginalPrimerReceipts.head p x l e a=
      if l≤e then diagonal cap (sprig (Near.meter p.atom x) p.r (e-l)) a else 0:=by
  by_cases active:l≤e
  · rw [WilsonOriginalPrimerReceipts.head,if_pos active,if_pos active,sprig_read _ _ _ _ within,Nat.add_comm]
    rfl
  · simp [WilsonOriginalPrimerReceipts.head,active]

end YM.Integration.WilsonNeutralTwoPrintPathJet
end
