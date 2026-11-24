import YM.Integration.WilsonMeasuredJointCensusCash

/-! Restrict a funded ordering of the actual lower transition coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCashRestriction
open QuadraticLocal Marker
open scoped Classical BigOperators
variable {V : Type} [Fintype V] {J:Census Unit} (s:J.Mode) (w:V→Unit→ℝ) (c:V→ℕ→ℝ) (b:V→ℝ)
def total (cap:ℕ) := WilsonEmittedJoinedFares.cash s (fun a:V×Fin (cap+1)=>w a.1)
  (fun a:V×Fin (cap+1)=>c a.1 a.2.val) (fun a:V×Fin (cap+1)=>b a.1)

theorem narrow {cutoff order:ℕ} (fits:cutoff≤order) (wp:∀v,0 ≤ Poly.toll (w v) s)
    (bp:∀v,0 ≤ b v) : total s w c b cutoff≤total s w c b order:=by
  classical
  unfold total WilsonEmittedJoinedFares.cash
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro v _
  let f (n:ℕ):=|c v n| * ((Poly.toll (w v) s)⁻¹*b v)
  change ∑n:Fin (cutoff+1),f n.val ≤ ∑n:Fin (order+1),f n.val
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ fits))
    (fun _ _ _=>mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr (wp v)) (bp v)))

end YM.Integration.WilsonMeasuredCashRestriction
end
