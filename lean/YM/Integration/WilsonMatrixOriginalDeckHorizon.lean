import YM.Integration.WilsonMatrixOriginalDeckStability

/-! Full-height perturbation over a growing sequence of physical reporting lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckHorizon
open Filter Set Finset Extraction Extraction.Order Spec Climb MS MS.Local.Physical MS.Menus MS.Land MS.Theater FVA2
open RG17 PhysicalNext.Repeat.Legato Trace.Pilot WilsonMatrixOriginalDeckPath WilsonMatrixOriginalDeckRelative
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (B:Deck G) {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

private theorem power_ratio {a b c:ℝ} (ha:0<a) (hb:0<b) (hc:0<c) (η:ℝ) :
    (a/b)^(-η)*(a/c)^η=(b/c)^η := by
  rw [Real.rpow_neg (div_nonneg ha.le hb.le),←Real.inv_rpow (div_nonneg ha.le hb.le),inv_div,
    ←Real.mul_rpow (div_nonneg hb.le ha.le) (div_nonneg ha.le hc.le)]
  congr 1
  field_simp

/-- For each height the forward telescope loses only the chosen η in the ratio of final/initial
lengths. It sees all intermediate grades before taking a low-to-high or high-to-low entry. -/
theorem original (lead:PhysMS.Leading F J) : ∃A:ℝ,1≤A ∧ ∀η:ℝ,0<η → ∃ready:Set ℝ,ready∈trail ∧
    ∀ (r:ℕ→ℝ) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ),
    (∀i,0<r i) → Monotone r → (∀i≤n,r i∈ready) →
      let U := fun i j=>WilsonMatrixOriginalDeckMixed.change B J h (r i) (r j)
      let D := ∑i∈range n,amount (V i-U (i+1) i)
      amount (steps V n-U n 0) ≤ A^2*(r n/r 0)^η*D*Real.exp (A*D) := by
  obtain ⟨A,hA,all⟩ := WilsonMatrixOriginalDeckRelative.original B F J h lead
  refine ⟨A,hA,?_⟩
  intro η hη
  obtain ⟨ready,window,pay⟩ := Filter.Eventually.exists_mem (all η hη)
  refine ⟨ready,window,?_⟩
  intro r V n positive ordered dates
  let U := fun i j=>WilsonMatrixOriginalDeckMixed.change B J h (r i) (r j)
  let w := fun i=> (r i/r 0)^η
  have wzero : w 0=1 := by simp [w,(positive 0).ne']
  have wn (i:ℕ) : 0≤w i := Real.rpow_nonneg (div_nonneg (positive i).le (positive 0).le) _
  have wm : Monotone w := fun i j hij=>Real.rpow_le_rpow (div_nonneg (positive i).le (positive 0).le)
    (div_le_div_of_nonneg_right (ordered hij) (positive 0).le) hη.le
  have whole (j:ℕ) (hj:j≤n) (i:ℕ) (hi:i≤j) : amount (U j i)*w i≤A*w j := by
    have ratio : r i/r j ∈ Ioc (0:ℝ) 1 := ⟨div_pos (positive i) (positive j),(div_le_one (positive j)).mpr (ordered hi)⟩
    have row := (pay (r j) (dates j hj) _ ratio).1
    rw [div_mul_cancel₀ _ (positive j).ne'] at row
    calc amount (U j i)*w i ≤ (A*(r i/r j)^(-η))*w i := mul_le_mul_of_nonneg_right row (wn i)
         _ = A*w j := by rw [mul_assoc];exact congrArg (A*·) (power_ratio (positive i) (positive j) (positive 0) η)
  exact WilsonMatrixOriginalDeckStability.measured U V w A n (fun i=>identity R B J h (r i))
    (fun i j k=>WilsonMatrixOriginalDeckReturn.compose R B J h (r i) (r j) (r k)) (by linarith) wzero wn wm whole

end YM.Integration.WilsonMatrixOriginalDeckHorizon
