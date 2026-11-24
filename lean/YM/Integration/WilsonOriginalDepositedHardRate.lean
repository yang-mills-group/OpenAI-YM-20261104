import YM.Integration.WilsonOriginalDepositedHardTable
import YM.RG01.Slack

/-! The actual original compulsory allowance pays restoration of the reporting radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedHardRate
open Function Filter Finset Lattice Wilson RG Source Marker QuadraticLocal
open WilsonOriginalDepositedHard
open scoped Topology BigOperators Classical
variable {G : Gauge} (simple : G.Simple) (A : Levels G)
include simple

theorem rooted (p : ℕ) : Tendsto (fun k => (A.clock.hatBeta k)^p * Real.sqrt (A.clock.forcedAllowance k))
    atTop (𝓝 0) := by
  have h := (RG01.Physical.shrink simple A (p*2)).sqrt
  rw [Real.sqrt_zero] at h
  refine h.congr fun i => ?_
  rw [pow_mul,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_nonneg (zero_le_one.trans (A.fits.delayed i).le) _)]

theorem restored (p q : ℕ) (C ε : ℝ) (margin : 0 < ε) :
    ∀ᶠ k in atTop, C*Real.sqrt (A.clock.forcedAllowance k)*(A.clock.hatBeta k)^p ≤
      ε*((A.clock.hatBeta k)^q)⁻¹ := by
  have h := (tendsto_const_nhds (x:=C)).mul (rooted simple A (p+q))
  rw [mul_zero] at h
  filter_upwards [h.eventually (ge_mem_nhds margin)] with k debit
  have pos : 0 < A.clock.hatBeta k := zero_lt_one.trans (A.fits.delayed k)
  rw [←div_eq_mul_inv,le_div_iff₀ (pow_pos pos q)]
  apply le_trans _ debit
  rw [pow_add]
  ring_nf
  exact le_rfl

theorem funded (p q₀ : ℕ) (C ε : ℝ) (margin : 0 < ε) :
    ∀ᶠ k in atTop, ∀ {n : Side} {d : ℕ} {F : Labels.Frame G d} {X : Hol G}
    {P : Rep G n} {V T : Type} [DecidableEq V] [Fintype V]
    {J : Census V} {o : V → Site n} (old : Hard T P.p P.activities.forced P.activities.K o J)
    (j : V) (q : Coefficient F n) (law : q.Format (o j) X P) (t : T → ℂ)
    (w : V → ℝ) (_hpos : ∀ i, 0 < w i) {B h : ℝ},
    old.Paid w P.p.B P.p.supportExponent h → (∀ x, ‖t x‖ ≤ 1) →
    q.remBound (o j) P (Real.sqrt (A.clock.forcedAllowance k)) B →
    w j*B ≤ C*(A.clock.hatBeta k)^p →
    (joined old j q law t).Paid w P.p.B P.p.supportExponent (h+ε*((A.clock.hatBeta k)^q₀)⁻¹) := by
  filter_upwards [restored simple A p q₀ C ε margin] with k cap n d F X P V T _ _ J o old j q law t w hw B h prior tested actual bill
  apply Hard.mono _ (paid old j q law t w hw prior tested actual)
  apply add_le_add (le_refl h)
  calc _ = Real.sqrt (A.clock.forcedAllowance k)*(w j*B) := by ring
       _ ≤ Real.sqrt (A.clock.forcedAllowance k)*(C*(A.clock.hatBeta k)^p) :=
         mul_le_mul_of_nonneg_left bill (Real.sqrt_nonneg _)
       _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using cap

end YM.Integration.WilsonOriginalDepositedHardRate
