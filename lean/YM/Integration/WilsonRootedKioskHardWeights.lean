import YM.Integration.WilsonRootedKioskSealedPost

/-! Restore the original marker weights on the entire hard family of the two
dated mergers, with the same dominating polynomial at every old address. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedKioskHardWeights
open Finset Lattice Wilson RG Marker QuadraticLocal Ac Push Push.AbsoluteSums ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V α:Type} [DecidableEq V] [Fintype V] {P:Rep G n}
  {o:V → Site n} {R:Census V} {w u:V → ℝ} {lower κ fee hard salary:ℝ}
  {model whole:α → Config G n → Poly R}

theorem restored
    (Z:WilsonRootedKioskSealedPost.Return P o R u lower κ fee hard model whole)
    (pos:∀j,0<w j) (small:∀j,0<Stoop.radius u κ j)
    (c:R.Mode → ℝ) (positive:∀s,0 ≤ c s)
    (tolls:∀s,Poly.toll (Stoop.radius u κ) s*c s=Poly.toll w s)
    (price:∀s,c s*hard ≤ salary):
    Z.output.K.Paid w P.p.B P.p.supportExponent salary := by
  obtain ⟨s,_,largest⟩:=univ.exists_max_image c ⟨R.quiet,mem_univ _⟩
  have withdrawn(f:Poly R):Poly.price w f ≤ c s*Poly.price (Stoop.radius u κ) f:=by
    unfold Poly.price
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    calc
      _ = c t*(Poly.toll (Stoop.radius u κ) t*‖f.part t‖) := by rw [←tolls t];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (largest t (mem_univ t))
        (mul_nonneg (Poly.worth small t).le (norm_nonneg _))
  obtain ⟨f,cover,rooted⟩:=Z.rates.wages.wages
  refine ⟨f,cover,fun x=>budget_loosen (budget_mono
    (budget_scale (positive s) (rooted x)) ?_ ?_) (price s)⟩
  · intro i
    split
    · exact mul_nonneg (Poly.nonnegative pos _) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    by_cases h:x∈(P.activities.forced i).support
    · simp only [if_pos h]
      exact (mul_le_mul_of_nonneg_right (withdrawn (f i)) (Real.exp_pos _).le).trans_eq (mul_assoc ..)
    · simp [h]

theorem temperature {x β:ℝ} (large:2 ≤ x) (warm:0<β) (band:β ≤ 2*x) (p:ℕ):
    x^(-(p:ℝ)) ≤ (Coat.gStep β)^p := by
  have strong:Real.sqrt β ≤ x := Real.sqrt_le_iff.mpr ⟨by linarith,by nlinarith⟩
  rw [Real.rpow_neg (by linarith : 0 ≤ x),Real.rpow_natCast,←inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
    (inv_anti₀ (Real.sqrt_pos.mpr warm) strong) p

end YM.Integration.WilsonRootedKioskHardWeights
