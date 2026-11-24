import YM.QuadraticLocal.Lamps
import YM.Comparison.RG02.Cumulants.Parents

/-! All connected modes containing a given mark on the actual regular Wilson
roster share one rooted income, including repeated physical addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredRegularHit
open RG Lattice Wilson QuadraticLocal Marker Ac Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V}
    {o : V → Site n} {p : BudgetPoint}

theorem rooted (L : Lamps X ι G p o R) (w : V → ℝ) (hw : ∀ i, 0 < w i)
    {a b : ℝ} (ha : 0 ≤ a) (paid : L.Paid w p.B a b) (t : X) (U : Config G n) (v : V) :
    Poly.price w (highlight v (L.log t U)) ≤ b := by
  obtain ⟨f, hf, caps, hit⟩ := paid.budget
  have total := hit (o v)
  let J : Poly R →L[ℂ] Poly R := (highlight v).toContinuousLinearMap
  have invoice (i : ι) : Poly.price w (J (L.frame i t U)) ≤
      if o v ∈ L.ground i then Poly.toll w (L.mode i) * f i *
        Real.exp (a * coverNumber p.B (L.ground i)) else 0 := by
    change Poly.price w (highlight v (Poly.send (L.mode i) (L.light t i U))) ≤ _
    rw [highlight_send]
    split_ifs with hv hv'
    · rw [Poly.solo]
      have W := (Poly.worth hw (L.mode i)).le
      have base := L.light_size i t U (caps i t _ (L.address i).anchor)
      exact (mul_le_mul_of_nonneg_left base W).trans
        (le_mul_of_one_le_right (mul_nonneg W (hf i))
          (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))))
    · exact (hv' (L.roots i v hv)).elim
    · rw [Poly.zero_price]
      exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hf i)) (Real.exp_pos _).le
    · exact Poly.zero_price.le
  have priced := Poly.budgeted hw total.2.1 invoice
  calc
    _ = Poly.price w (∑' i, J (L.frame i t U)) :=
      congrArg (Poly.price w) (J.map_tsum (paid.sums ha hw t U))
    _ ≤ _ := priced.2.trans total.2.2

theorem component (L : Lamps X ι G p o R) (w : V → ℝ) (hw : ∀ i, 0 < w i)
    {a b : ℝ} (ha : 0 ≤ a) (paid : L.Paid w p.B a b) (t : X) (U : Config G n)
    (M : R.Mode) (v : V) (hv : v ∈ M.val) :
    ‖(L.log t U).part M‖ ≤ (Poly.toll w M)⁻¹ * b := by
  have h := (Poly.member hw M (highlight v (L.log t U))).trans (rooted L w hw ha paid t U v)
  rw [highlight_part, if_pos hv] at h
  calc
    _ = (Poly.toll w M)⁻¹ * (Poly.toll w M * ‖(L.log t U).part M‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (Poly.worth hw M).ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Poly.worth hw M).le)

end YM.Integration.WilsonCenteredRegularHit
