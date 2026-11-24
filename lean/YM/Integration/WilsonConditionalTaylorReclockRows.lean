import YM.Integration.WilsonConditionalTaylorKineticHead
import YM.FormalBulk08.Wine.Cab

/-! Identification of the physical coupling reset with the formal
rebooking on the whole field, including its classical quadratic. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorReclockRows
open PowerSeries FormalBulk08 Orb Reef Jets Lava Shore Wine MSbar MSbar.Wave
open scoped Classical BigOperators
variable {V : Type} [Fintype V]

private theorem projected (r d : ℕ) (P : MvPolynomial V ℝ) :
    canyon r (MvPolynomial.homogeneousComponent d P) = if r=d then canyon r P else 0 := by
  by_cases eq : r=d
  · subst d
    rw [if_pos rfl, ← marble_grade r P]
    exact marble_rec r _ (marble_agate _ _)
  · rw [if_neg eq,canyon_eq,marble_eq_zero_iff,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.homogeneousComponent_isHomogeneous ..),if_neg eq]

private theorem charged (b : PowerSeries ℝ) (T : Pap V) (i j r : ℕ)
    (h : i+2 < r → rancho T i r=0) :
    canyon r (Wave.fare b T i j) = coeff j ((b⁻¹)^i * b^r) • rancho T i r := by
  simp only [Wave.fare,map_sum,map_smul,projected]
  by_cases hr : r ≤ i + 2
  · rw [Finset.sum_eq_single r]
    · rw [if_pos rfl,mul_comm]
      rfl
    · intro d hd other
      rw [if_neg (Ne.symm other),smul_zero]
    · intro out
      exact False.elim (out (Finset.mem_range.mpr (by omega)))
  · rw [h (by omega),smul_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have := Finset.mem_range.mp hd
    rw [if_neg (by omega : r≠d),smul_zero]

theorem ticket (b : PowerSeries ℝ) (T : Pap V) (e r : ℕ)
    (h : ∀ i ≤ e, i + 2 < r → rancho T i r=0) :
    rancho (Wave.ticket b T) e r = rancho (Wine.canter b⁻¹ b V T) e r := by
  rw [stamp_book]
  change canyon r (coeff e (Wave.ticket b T))=_
  rw [Wave.ticket,coeff_mk,map_sum,stamp]
  exact Finset.sum_congr rfl (fun i hi=>charged b T i (e-i) r (h i (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi)))

private theorem classicalRow (b : PowerSeries ℝ) (Q : MvPolynomial V ℝ)
    (hq : Q.IsHomogeneous 2) (e r : ℕ) :
    rancho (Wine.canter b⁻¹ b V (C Q)) e r = coeff e (b^2) • canyon r Q := by
  rw [stamp_book,stamp,Finset.sum_eq_single 0]
  · change coeff (e-0) ((b⁻¹)^0 * b^r) • canyon r (coeff 0 (C Q)) = _
    rw [Nat.sub_zero,pow_zero,one_mul,coeff_zero_C]
    by_cases hr : r=2
    · rw [hr]
    · have hz : canyon r Q=0:=by rw [canyon_eq,marble_eq_zero_iff,MvPolynomial.homogeneousComponent_of_mem hq,if_neg hr]
      rw [hz,smul_zero,smul_zero]
  · intro j hj pos
    change _ • canyon r (coeff j (C Q))=0
    rw [coeff_C,if_neg pos,map_zero,smul_zero]
  · intro missing
    exact False.elim (missing (Finset.mem_range.mpr (by omega)))

theorem restored (b : PowerSeries ℝ) (T : Pap V) (Q : MvPolynomial V ℝ)
    (hq : Q.IsHomogeneous 2) {e : ℕ} (positive : 0<e) (r : ℕ)
    (h : ∀ i ≤ e, i + 2 < r → rancho T i r=0) :
    rancho (Wave.bley b T Q) e r = rancho (Wine.canter b⁻¹ b V (T - C Q)) e r := by
  have switched := ticket b T e r h
  have base := classicalRow b Q hq e r
  change canyon r (coeff e (Wave.bley b T Q))=canyon r (coeff e (Wine.canter b⁻¹ b V (T - C Q)))
  rw [Wave.bley,map_sub,map_sub,coeff_mk,map_smul,map_sub,map_sub,map_sub,map_sub]
  change rancho (Wave.ticket b T) e r - (coeff e (b^2) - coeff e (1:PowerSeries ℝ)) • canyon r Q =
    rancho (Wine.canter b⁻¹ b V T) e r - rancho (Wine.canter b⁻¹ b V (C Q)) e r
  rw [switched,base,coeff_one,if_neg positive.ne',sub_zero]

end YM.Integration.WilsonConditionalTaylorReclockRows

