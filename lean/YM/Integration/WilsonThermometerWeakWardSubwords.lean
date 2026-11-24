import YM.Integration.WilsonThermometerReflectedWatch
/-! Keep every cleared chamber of the same exterior in every signed Ward subword of an arbitrary finite roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardSubwords
open Function Filter Set MeasureTheory Finset Lattice Wilson Cells WilsonThermometerReflectedProducts
open scoped BigOperators Classical

open WilsonThermometerReflectedWatch (exterior)
variable {I : Type*} [Fintype I] {G : Gauge} {n : Side} {J : Type*} [Fintype J]
    (T : Tiling n) (v : I → T.Cell) (q : J → T.Cell) (P D : I → Config G n → ℂ)
    (W : J → Config G n → ℂ) (β : ℝ)


theorem original (seam : Seam G n β) (distinct : Injective (Sum.elim v q))
    (hP : ∀ i, Interior (T.chamber 0) (P i)) (hD : ∀ i, Interior (T.chamber 0) (D i))
    (hW : ∀ j, Interior (T.chamber 0) (W j))
    {M : I → ℝ} {δ : ℝ} (positive : ∀i,0 ≤ M i) (small : δ ≤ 1)
    (standard : ∀ i,T.rootTest β (P i) ≤ M i) (error : ∀ i,T.rootTest β (D i) ≤ δ*M i) :
    ‖moment β (fun U=>(∏ i, (T.copy (v i) (P i) U-T.copy (v i) (D i) U)) * exterior T q W U) -
      moment β (fun U=>(∏ i, T.copy (v i) (P i) U)*exterior T q W U)‖ ≤
      (((2:ℕ)^Fintype.card I-1:ℕ):ℝ)*(δ*∏ i,M i)*(∏ j,T.rootTest β (W j)) := by
  classical
  let X (i:I) := (-1:ℂ) • D i
  have localX (i:I) : Interior (T.chamber 0) (X i) := (hD i).scale _
  have negPrice (i:I) : T.rootTest β (X i) = T.rootTest β (D i) := by
    change T.rootTest β ((-1:ℂ) • D i) = _
    rw [Next.Extract.root_smul]; simp
  have copyX (i : I) (U : Config G n) : T.copy (v i) (X i) U = -T.copy (v i) (D i) U := by
    unfold Tiling.copy X
    split_ifs <;> simp
  have legal (s : Finset (I)) (i:I) : Interior (T.chamber 0) (branch P X s i) := by
    by_cases hi:i∈s <;> simp only [branch,hi,if_true,if_false] <;> first | exact hP i | exact localX i
  have room (s : Finset (I)) : Interior Set.univ (fun U=>word T v P X s U*exterior T q W U) :=
    (Interior.combines (K:=Set.univ) (fun i=> T.copy (v i) (branch P X s i)) univ fun i _=>
      (T.copies (v i) (legal s i)).enlarges (subset_univ _)).times
    (Interior.combines (K:=Set.univ) (fun j=> T.copy (q j) (W j)) univ fun j _=>
      (T.copies (q j) (hW j)).enlarges (subset_univ _))
  have joined (s : Finset (I)) : ‖moment β (fun U=>word T v P X s U*exterior T q W U)‖ ≤
      (∏ i,T.rootTest β (branch P X s i))*(∏ j,T.rootTest β (W j)) := by
    have get := T.planted seam (Sum.elim v q) distinct (Sum.elim (branch P X s) W)
      (fun a=>by cases a with | inl i=>exact legal s i | inr j=>exact hW j)
    simpa only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,word,exterior] using get
  have allTerms (U) :
      (∏ i, (T.copy (v i) (P i) U-T.copy (v i) (D i) U))*exterior T q W U =
      ∑ s : Finset (I), word T v P X s U*exterior T q W U := by
    have full := split T v P X U
    simp only [copyX,←sub_eq_add_neg] at full
    rw [full,Finset.sum_mul]
  have table : moment β (fun U=>(∏ i, (T.copy (v i) (P i) U-T.copy (v i) (D i) U))*exterior T q W U) =
      ∑ s : Finset (I),moment β (fun U=>word T v P X s U*exterior T q W U) := by
    simp only [moment,allTerms]
    exact integral_finsetSum _ (fun s _=>(room s).integrable β)
  have blank : word T v P X ∅ = fun U=>∏ i,T.copy (v i) (P i) U := by
    funext U; simp [word,branch]
  let S := (Finset.univ : Finset (Finset (I))).erase ∅
  have cut := Finset.sum_erase_add (s:=univ) (fun s=>moment β (fun U=>word T v P X s U*exterior T q W U))
    (Finset.mem_univ (∅ : Finset (I)))
  have empty : moment β (fun U=>(∏ i,T.copy (v i) (P i) U)*exterior T q W U) =
      moment β (fun U=>word T v P X ∅ U*exterior T q W U) := by simp only [blank]
  rw [table,empty,←cut,add_sub_cancel_right]
  have each {s : Finset (I)} (hs : s∈S) : (∏ i, T.rootTest β (branch P X s i)) ≤ δ*∏ i,M i := by
    obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr ((Finset.mem_erase.mp hs).1)
    calc
      _ ≤ ∏ i : I, (if i=j then δ else 1)*M i := by
        apply Finset.prod_le_prod (fun i _ => T.root_nonneg β _)
        intro i _
        by_cases eq:i=j
        · subst i; simpa [branch,hj,negPrice] using error j
        · by_cases included : i∈s
          · simpa [branch,included,eq,negPrice] using (error i).trans (mul_le_of_le_one_left (positive i) small)
          · simpa [branch,included,eq] using standard i
      _ = δ*∏ i,M i := by rw [Finset.prod_mul_distrib];simp
  have count : S.card=(2:ℕ)^Fintype.card I-1 := by simp [S,Finset.card_erase_of_mem (Finset.mem_univ _),Fintype.card_finset]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ ∈ S, (δ*∏ i,M i)*(∏ j,T.rootTest β (W j)) := Finset.sum_le_sum fun s hs=>
      (joined s).trans (mul_le_mul_of_nonneg_right (each hs) (Finset.prod_nonneg fun j _=>T.root_nonneg β _))
    _ = _ := by rw [Finset.sum_const,count]; simp only [nsmul_eq_mul]; ring

end YM.Integration.WilsonThermometerWeakWardSubwords
