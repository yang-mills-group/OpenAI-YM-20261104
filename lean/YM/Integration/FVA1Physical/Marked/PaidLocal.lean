import YM.Integration.FVA1Physical.Marked.SupportCredit

/-! Pay every local stencil invoice at fixed total source degree. The
normalised independent weights undo the actual source-ray scaling. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Pressure Finset Marker Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset
open ConnectedActivityE6
open scoped BigOperators Classical Topology
variable {V M : Type} [DecidableEq V] [Fintype V] [Fintype M] {B : Census V}

omit [Fintype V] in
theorem invoice_polynomial (G : Gauge) (ξ : V → ℕ) (qd b : ℕ) (s : Senses B)
    {g t : ℝ} (hg : 0 < g) (h1 : g ≤ 1) (h : g⁻¹ ≤ t) :
    valueInvoice G ξ qd b s g ≤ valueInvoice G ξ qd b s 1 * t^(Lagger.dues ξ s.val) := by
  unfold valueInvoice
  simp only [one_pow, div_one, abs_one, one_mul]
  rw [sum_mul]
  apply sum_le_sum
  intro e _
  rw [sum_mul]
  apply sum_le_sum
  intro n _
  let d := Lagger.dues ξ s.val
  have hr : 0 ≤ g^(e.val+d-n.val) / g^d := div_nonneg (pow_nonneg hg.le _) (pow_nonneg hg.le _)
  rw [abs_of_nonneg hr, div_eq_mul_inv, ← inv_pow, mul_comm (Vase.ticketC G b n.val)]
  apply mul_le_mul_of_nonneg_right _ (Vase.ticketC_pos ..)
  exact (mul_le_of_le_one_left (pow_nonneg (inv_pos.mpr hg).le _) (pow_le_one₀ hg.le h1)).trans
    (pow_le_pow_left₀ (inv_pos.mpr hg).le h _)

omit [Fintype V] in
theorem invoice_product (G : Gauge) (ξ : V → ℕ) (qd b : ℕ) (modes : M → Senses B)
    (ray : B.Mode → ℝ) (hray : ∀ s, 0 < ray s) {y β τ : ℝ} (hy : 2 ≤ y)
    (hβ : y/2 ≤ β ∧ β ≤ 2*y) (ht : Real.exp τ ≤ y^3) :
    (∏ s, ray (modes s).val) * (∏ s, Real.exp τ * ((ray (modes s).val)⁻¹ * valueInvoice G ξ qd b (modes s) (Coat.gStep β))) ≤
      (∏ s, 2^(Lagger.dues ξ (modes s).val) * valueInvoice G ξ qd b (modes s) 1) *
      y^(3 * Fintype.card M + ∑ s, Lagger.dues ξ (modes s).val) := by
  let g := Coat.gStep β
  have hβ1 : 1 ≤ β := by linarith [hβ.1]
  have hh : 0 < β := zero_lt_one.trans_le hβ1
  have hs : 1 ≤ Real.sqrt β := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hβ1
  have hl : Real.sqrt β ≤ β := (Real.sqrt_le_left hh.le).mpr (by nlinarith)
  have h0 : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hh)
  have h1 : g ≤ 1 := inv_le_one_of_one_le₀ hs
  have hi : g⁻¹ ≤ 2*y := by simpa only [g,Coat.gStep,inv_inv] using hl.trans hβ.2
  have nonneg (s : M) (x : ℝ) : 0 ≤ valueInvoice G ξ qd b (modes s) x :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..)
  let d := fun s : M => Lagger.dues ξ (modes s).val
  have hloc (s : M) : ray (modes s).val * (Real.exp τ * ((ray (modes s).val)⁻¹ *
    valueInvoice G ξ qd b (modes s) g)) ≤
    (2^(d s)*valueInvoice G ξ qd b (modes s) 1) * y^(3+d s) := by
    rw [show ray (modes s).val * (Real.exp τ * ((ray (modes s).val)⁻¹ * valueInvoice G ξ qd b (modes s) g)) =
      Real.exp τ*valueInvoice G ξ qd b (modes s) g by field_simp [(hray _).ne']]
    apply (mul_le_mul ht (invoice_polynomial G ξ qd b (modes s) h0 h1 hi) (nonneg s g) (by positivity)).trans_eq
    rw [mul_pow, pow_add]; ring
  rw [← prod_mul_distrib]
  apply (prod_le_prod (fun s _ => mul_nonneg (hray _).le <| mul_nonneg (Real.exp_pos _).le <|
    mul_nonneg (inv_pos.mpr (hray _)).le (nonneg s g)) (fun s _ => hloc s)).trans_eq
  simp only [prod_mul_distrib,prod_pow_eq_pow_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,d]
  congr 2
  norm_cast
  omega
end YM.Integration.FVA1Physical.Marked
