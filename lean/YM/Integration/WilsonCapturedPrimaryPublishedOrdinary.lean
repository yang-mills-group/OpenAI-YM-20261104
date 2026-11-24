import YM.Integration.WilsonReceivedOrdinaryPanel
import YM.Integration.WilsonReceivedCloseOrdinaryGrade
import YM.Integration.WilsonCapturedPrimaryPublishedLog

/-! Ordinary published rows on the very finite Wick table, with truncation
after the whole partition product and a tariff at each nonquiet face. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPublishedOrdinary
open Function Finset RG Lattice Wilson Marker Multi Extra.Trajectories Comparison.RG02
open Comparison.RG02.Order Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade QuadraticLocal Ac
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V} {r : ℕ}

omit [Fintype V] in
theorem quiet {G : Gauge} {n : Side} {o : V→Site n} {p : BudgetPoint} {X ι : Type}
    (L : Lamps X ι G p o J) (x : X) (U : Config G n) : (L.log x U).part J.quiet=0 := by
  by_cases h : Summable (fun i=>L.frame i x U)
  · exact L.quiet_of_hasSum x U h
  · simp [Lamps.log,tsum_eq_zero_of_not_summable h]

theorem original (L : Poly J) (zero : L.part J.quiet=0) (W : Grade J r)
    (unitW : UnitLeading W) (sym : Symmetric W) (w : V→ℝ) (hw : ∀v,0<w v)
    (g : ℝ) (gp : 0<g) (small : g≤1) (s : J.Mode) (a q : ℕ) (fixed : s.val.card≤a)
    (grades : a+q+1≤r+1)
    (fund : ∀t : Multi.Hot J, t.val.val⊆s.val →
      g*(Poly.toll w t.val*mass (slot t.val (Order.render (Order.logMarked W))))≤1)
    (logs : ∀t : Multi.Hot J, t.val.val⊆s.val → Poly.toll w t.val*
        ‖(L-Order.value (g:ℂ) (Order.logMarked W)).part t.val‖≤g^(q+1+a)) :
    Poly.toll w s * ‖(Poly.pass L).part s - (Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
      WilsonReceivedCloseOrdinaryGrade.invoice J a 0 q 1*g^(q+1) := by
  have logged : Order.logTo (Fintype.card V) (Poly.pass L)=L := by
    rw [←Order.log_to _ (Poly.pass_part _ zero) _ (fun s=>card_le_univ _),Comparison.RG02.Cumulants.connected_pass zero]
  have debts (t : Multi.Hot J) (inside : t.val.val⊆s.val) : Poly.toll w t.val*
      ‖(Order.logTo (Fintype.card V) (Poly.pass L)-Order.value (g:ℂ) (Order.logMarked W)).part t.val‖≤g^(q+1+a) := by
    rw [logged]
    exact logs t inside
  have purchase := WilsonReceivedOrdinaryPanel.measured_on (Poly.pass L) (Poly.pass_part _ zero) W unitW sym
    w hw g (g^(q+1+a)) gp small (pow_nonneg gp.le _) s fund debts
    (q+1) (by omega)
  have edge : g≤3*g := by linarith only [gp]
  have inverse : g⁻¹≤3*g⁻¹ := by linarith only [inv_pos.mpr gp]
  apply WilsonReceivedCloseOrdinaryGrade.earned J s a 0 q (U:=1) (t:=g) le_rfl gp small gp edge inverse fixed
  simpa only [Nat.zero_mul,Nat.add_zero,pow_zero,one_mul,one_pow] using purchase

end YM.Integration.WilsonCapturedPrimaryPublishedOrdinary
