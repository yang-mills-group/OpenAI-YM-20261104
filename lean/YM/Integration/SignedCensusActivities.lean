import YM.Integration.CensusTailExtraction
import YM.Integration.ActualRunVacuumNorm

/-! Signed activity transfer between two physical representatives with the
same background and an explicitly recorded action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedCensusActivities

open Lattice Wilson RG Push.AbsoluteSums AnalyticBridge VerifiedReset Collection
open Averaging Quotes Residual IterationFour.Vacuum UVNext.CouplingReset

variable {G : Gauge} {n : Side}

/-- The site's charged majorant pays every masked summand in the signed
additive action on an arbitrary configuration of this finite torus. -/
theorem additive (A : Activities G n) (p : BudgetPoint) {H : ℝ}
    (h : A.EBound p H) (z : Config G n) : |A.additive p z| ≤ sites n * H := by
  obtain ⟨u,hu,hE⟩ := h
  have hsum := CouplingShape.totalBooked (p := p) (u := A.reg) (fun i => (hu i).1)
    hE
  have hb : SumBudget (fun i => |A.regularOccurrence p i z|) (sites n*H) := by
    refine budget_mono hsum (fun i => abs_nonneg _) ?_
    intro i
    by_cases live : Healthy p.threshold (A.reg i).support z
    · rw [Activities.regularOccurrence,masked_eq _ _ _ _ live]
      exact (hu i).2 z live [] (by simp) (by simp)
    · rw [Activities.regularOccurrence,masked_ne _ _ _ _ live, abs_zero]
      exact (hu i).1
  exact (norm_tsum_le_tsum_norm (f := fun i => A.regularOccurrence p i z) hb.2.1).trans hb.2.2

theorem channels (W : PathData G) (c : Clip) (p q : BudgetPoint)
    (ht : p.threshold = q.threshold) (b : ℝ) (z : Config G n) :
    W.inChannels c p b z = W.inChannels c q b z := by
  cases p
  cases q
  cases ht
  rfl

/-- Preserve the signed gas on the original hard inventory and identify its
exact multiplier under the physical change of regular activity. This equality
also applies when the hard gas vanishes or has negative sign. -/
theorem gas (Y Z : Rep G n) (hv : Z.v = Y.v) (hb : Z.beta = Y.beta)
    (hw : Z.path = Y.path) (hc : Z.clip = Y.clip) (ht : Z.p.threshold = Y.p.threshold)
    (f : Config G n → ℝ) (he : ∀ z, Y.eval z = Z.eval z * Real.exp (-f z))
    (z : Config G n) :
    Y.activities.gas Y.p z = Z.activities.gas Z.p z *
      Real.exp (Y.activities.additive Y.p z-Z.activities.additive Z.p z-f z) := by
  have hkin : Z.path.inChannels Z.clip Z.p Z.beta z = Y.path.inChannels Y.clip Y.p Y.beta z := by
    rw [hw,hc,hb]
    exact channels _ _ _ _ ht _ _
  let a := Y.activities.additive Y.p z
  let b := Z.activities.additive Z.p z
  have hex : Z.exponent z = Y.exponent z + (a-b) := by
    unfold Rep.exponent
    rw [hv,hkin]
    dsimp only [a,b]
    ring
  have hfact : Real.exp (a-b-f z) = Real.exp (a-b) * Real.exp (-f z) := by
    rw [sub_eq_add_neg (a-b) (f z),Real.exp_add]
  apply mul_left_cancel₀ (Real.exp_pos (Y.exponent z)).ne'
  calc
    _ = Y.eval z := rfl
    _ = Z.eval z * Real.exp (-f z) := he z
    _ = _ := by
      rw [Rep.eval,hex,Real.exp_add,hfact]
      ring

/-- On a small field the signed retained action is exactly the difference
of regular actions. Its volume-normalized bound uses both actual invoices. -/
theorem healthy (Y Z : Rep G n) (hv : Z.v = Y.v) (hb : Z.beta = Y.beta)
    (hw : Z.path = Y.path) (hc : Z.clip = Y.clip) (ht : Z.p.threshold = Y.p.threshold)
    {δY δZ : ℝ} (hY : Y.activities.EBound Y.p δY) (hZ : Z.activities.EBound Z.p δZ)
    (f : Config G n → ℝ) (he : ∀ z, Y.eval z = Z.eval z * Real.exp (-f z))
    (z : Config G n) (hz : flags Y.p.threshold z = ∅) :
    f z = Y.activities.additive Y.p z - Z.activities.additive Z.p z ∧
      |f z| ≤ sites n*(δY+δZ) := by
  have h := gas Y Z hv hb hw hc ht f he z
  rw [Y.activities.gas_one Y.p hz,Z.activities.gas_one Z.p (ht.symm ▸ hz),one_mul] at h
  have h0 := Real.exp_injective (Real.exp_zero.trans h)
  have heq : f z = Y.activities.additive Y.p z - Z.activities.additive Z.p z := by linarith only [h0]
  refine ⟨heq,?_⟩
  rw [heq,mul_add]
  exact (abs_sub _ _).trans (add_le_add (additive _ _ hY _) (additive _ _ hZ _))

end YM.Integration.SignedCensusActivities
end
