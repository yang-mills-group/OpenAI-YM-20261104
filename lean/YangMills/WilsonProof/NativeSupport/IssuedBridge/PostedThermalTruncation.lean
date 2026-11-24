import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedCouplingPowers

namespace IssuedBridge.PostedThermalTruncation
open YM.MS Finset
open scoped BigOperators Classical
noncomputable section

theorem above (c : Book.Program.Cn) (zero : PowerSeries.coeff 0 c = 0)
    {j d : ℕ} (later : d < j) : Book.Program.cut c j d = 0 := by
  obtain ⟨u,rfl⟩ := PowerSeries.X_dvd_iff.mpr ((PowerSeries.coeff_zero_eq_constantCoeff_apply c).symm.trans zero)
  rw [Book.Program.cut, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (Nat.not_le.mpr later)]

theorem original (c : Book.Program.Cn) (zero : PowerSeries.coeff 0 c = 0)
    {T : Type*} [AddCommGroup T] [Module ℂ T] (A : ℕ → T) {d k : ℕ} (hd : d ≤ k) :
    (Book.Program.substitute c A) d = ∑ j : Fin (k+1), Book.Program.cut c j.val d • A j.val := by
  classical
  change ∑ j ∈ Iic d, Book.Program.cut c j d • A j =
    ∑ j : Fin (k+1), (fun j : ℕ => Book.Program.cut c j d • A j) j.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Book.Program.cut c j d • A j) (k+1)]
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.mem_Iic.mp hj).trans hd))
  · intro j _ hj
    have late := Nat.lt_of_not_ge (fun h => hj (Finset.mem_Iic.mpr h))
    rw [above c zero late, zero_smul]
end
end IssuedBridge.PostedThermalTruncation
