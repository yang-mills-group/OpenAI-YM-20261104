import YM.Integration.WilsonThermometerReflectedProducts
import YM.Next.EXTRACTION.Basis

/-! After exact Haar erasure, use the unchanged measured columns as the
other factors in each signed reflected word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReflectedChange
open Function Finset Lattice Wilson Cells WilsonThermometerReflectedProducts
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} (T : Tiling n) (c : Fin 3 → T.Cell)
    (P D : Fin 3 → Config G n → ℂ) (β : ℝ)

theorem original (seam : Seam G n β) (distinct : Injective c)
    (hP : ∀ i, Interior (T.chamber 0) (P i)) (hD : ∀ i, Interior (T.chamber 0) (D i))
    {M δ : ℝ} (positive : 0 ≤ M) (small : δ ≤ 1)
    (standard : ∀ i,T.rootTest β (P i) ≤ M) (error : ∀ i,T.rootTest β (D i) ≤ δ*M) :
    ‖moment β (fun U=>∏ i, (T.copy (c i) (P i) U-T.copy (c i) (D i) U)) -
      moment β (fun U=>∏ i, T.copy (c i) (P i) U)‖ ≤ 7*(δ*M^3) := by
  classical
  let X (i:Fin 3) := (-1:ℂ) • D i
  have localX (i:Fin 3) : Interior (T.chamber 0) (X i) := (hD i).scale _
  have negPrice (i:Fin 3) : T.rootTest β (X i) = T.rootTest β (D i) := by
    change T.rootTest β ((-1:ℂ) • D i) = _
    rw [Next.Extract.root_smul]
    simp
  have copyX (i : Fin 3) (U : Config G n) : T.copy (c i) (X i) U = -T.copy (c i) (D i) U := by
    unfold Tiling.copy X
    split_ifs <;> simp
  have bill := priced T c P X β seam distinct hP localX
  simp only [copyX,←sub_eq_add_neg] at bill
  apply bill.trans
  let S := (Finset.univ : Finset (Finset (Fin 3))).erase ∅
  have individual {s : Finset (Fin 3)} (hs : s∈S) :
      (∏ i, T.rootTest β (branch P X s i)) ≤ δ*M^3 := by
    obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr ((Finset.mem_erase.mp hs).1)
    calc
      _ ≤ ∏ i : Fin 3, if i=j then δ*M else M := by
        apply Finset.prod_le_prod (fun i _ => T.root_nonneg β _)
        intro i _
        by_cases eq:i=j
        · subst i
          simpa [branch,hj,negPrice] using error j
        · by_cases included : i∈s
          · simpa [branch,included,eq,negPrice] using
              (error i).trans (mul_le_of_le_one_left positive small)
          · simpa [branch,included,eq] using standard i
      _ = δ*M^3 := by fin_cases j <;> simp [Fin.prod_univ_succ] <;> ring
  have count : S.card=7 := by
    simp [S,Finset.card_erase_of_mem (Finset.mem_univ _), Fintype.card_finset]
  calc
    _ ≤ ∑ _ ∈ S, δ*M^3 := Finset.sum_le_sum fun _ hs=>individual hs
    _ = _ := by rw [Finset.sum_const,count]; simp only [nsmul_eq_mul,Nat.cast_ofNat]

end YM.Integration.WilsonThermometerReflectedChange
