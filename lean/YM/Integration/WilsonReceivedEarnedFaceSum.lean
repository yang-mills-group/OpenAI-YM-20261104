import YM.Integration.WilsonReceivedCloseCoissuedOrdinary

/-! Sum the independently signed face coefficients after the original received
marker radii have been returned on their common post. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedEarnedFaceSum
open Tree Marker QuadraticLocal QuadraticLocal.Mentor Comparison.RG02 Finset
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V]

theorem original (w:V→ℝ) {g:ℝ} (gp:0<g) (unit:g≤1)
    (d a h:ℕ) (sold:∀s:(Stock.census V).Mode,g^(d*s.val.card+1)≤Poly.toll w s)
    (faces:Finset (Stock.census V).Mode) (c:(Stock.census V).Mode→ℂ)
    (arity:∀s∈faces,s.val.card≤a) :
    g^(h+(d*a+1))*(∑s∈faces,‖c s‖/Poly.toll w s) ≤ g^h*(∑s∈faces,‖c s‖) := by
  have each (s:(Stock.census V).Mode) (inList:s∈faces) : g^(d*a+1) ≤ Poly.toll w s := by
    apply le_trans _ (sold s)
    exact pow_le_pow_of_le_one gp.le unit (Nat.add_le_add_right (Nat.mul_le_mul_left d (arity s inList)) 1)
  rw [pow_add, mul_assoc, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg gp.le _)
  apply Finset.sum_le_sum
  intro s hs
  rw [←mul_div_assoc, div_le_iff₀ ((pow_pos gp _).trans_le (each s hs)), mul_comm]
  exact mul_le_mul_of_nonneg_left (each s hs) (norm_nonneg _)

end YM.Integration.WilsonReceivedEarnedFaceSum
