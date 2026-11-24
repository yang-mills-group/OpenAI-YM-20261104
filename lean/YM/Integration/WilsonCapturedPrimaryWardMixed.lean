import YM.Integration.WilsonCapturedPrimaryWardNest

/-! The full Haar-equation restoration on its actual repeated cell, including
each mixed residual term with its original sign. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardMixed
open Function Filter Set Cells Wilson Lattice Finset
open scoped Topology BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma expansion (f g : I → ℂ) :
    (∏ i, f i) - ∏ i, (f i-g i) =
      ∑ t ∈ (univ : Finset (Finset I)).erase ∅, -((-1:ℂ)^t.card) * ∏ i, t.piecewise g f i := by
  classical
  let term (t : Finset I) : ℂ := (-1)^t.card * ∏ i,t.piecewise g f i
  have terms : (∏ i,(f i-g i)) = ∑ t:Finset I,term t := by
    rw [Finset.prod_sub]
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [term]
    rw [Finset.prod_piecewise]
    simp only [Finset.univ_inter]
    ring
  have split := Finset.sum_erase_add (univ : Finset (Finset I)) term (Finset.mem_univ (∅ : Finset I))
  have zero : term ∅ = ∏ i,f i := by simp [term]
  rw [terms,←split,zero]
  have negative : ∑ t ∈ (univ : Finset (Finset I)).erase ∅, -((-1:ℂ)^t.card) * ∏ i,t.piecewise g f i =
      -∑ t ∈ (univ : Finset (Finset I)).erase ∅,term t := by simp only [term,neg_mul,Finset.sum_neg_distrib]
  rw [negative]
  abel

private lemma price (t : Finset I) (hit : t ≠ ∅) (g : I → ℝ) (nonneg : ∀ i, 0 ≤ g i)
    {δ : ℝ} (pos : 0 ≤ δ) (small : δ ≤ 1) :
    ∏ i,t.piecewise (fun j=>δ*g j) g i ≤ δ*∏ i,g i := by
  classical
  obtain ⟨i,key⟩ := Finset.nonempty_iff_ne_empty.mpr hit
  let part (j : I) := if j = i then δ else 1
  have cheap : ∏ j,t.piecewise (fun h=>δ*g h) g j ≤ ∏ j,part j*g j := by
    apply Finset.prod_le_prod
    · intro j _
      by_cases hj : j∈t <;> simp [hj,Finset.piecewise,pos,nonneg,mul_nonneg]
    · intro j _
      by_cases h:j=i
      · subst j
        simp [part, key, Finset.piecewise]
      · by_cases hj:j∈t
        · simpa [part,hj,h,Finset.piecewise] using mul_le_mul_of_nonneg_right small (nonneg j)
        · simp [part,hj,h,Finset.piecewise]
  rw [Finset.prod_mul_distrib] at cheap
  have root : ∏ j,part j = δ := by simp [part]
  rwa [root] at cheap

/-- It suffices to buy one small native equation in each occupied pattern from a fine
chessboard. All products here live on one Wilson configuration and one denominator. -/
theorem original {G : Gauge} {n : Side} (T : Cells.Tiling n) (β : ℝ) (seam : Seam G n β)
    (f g : I → Config G n → ℂ) (fee : I → ℝ) (nonneg : ∀ i, 0 ≤ fee i)
    (left : ∀ i, Interior (T.chamber 0) (f i)) (right : ∀ i, Interior (T.chamber 0) (g i))
    {δ : ℝ} (pos : 0 ≤ δ) (small : δ ≤ 1)
    (bought : ∀ t : Finset I, t ≠ ∅ →
      T.rootTest β (∏ i,t.piecewise g f i) ≤ ∏ i,t.piecewise (fun j=>δ*fee j) fee i) :
    Interior (T.chamber 0) ((∏ i,f i) - ∏ i,(f i-g i)) ∧
      T.rootTest β ((∏ i,f i) - ∏ i,(f i-g i)) ≤
        (((2:ℕ)^Fintype.card I-1:ℕ):ℝ)*δ*∏ i,fee i := by
  classical
  let rest := (univ : Finset (Finset I)).erase ∅
  let atField (t:Finset I) := ∏ i,t.piecewise g f i
  let sign (t:Finset I) : ℂ := -((-1)^t.card)
  have same : (∏ i,f i) - (∏ i,(f i - g i)) = ∑ t ∈ rest,sign t • atField t := by
    funext U
    change (∏ i,f i) U - (∏ i,(f i-g i)) U = _
    simp only [atField,sign,Pi.sub_apply,Finset.prod_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    convert expansion (fun i=>f i U) (fun i=>g i U) using 1
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i∈t <;> simp [Finset.piecewise,h]
  have safe (t : Finset I) : Interior (T.chamber 0) (atField t) := by
    rw [show atField t = fun U=>∏ i,t.piecewise g f i U by funext U; simp [atField]]
    apply Interior.combines _ univ
    intro i _
    by_cases h : i∈t
    · simpa [Finset.piecewise,h] using right i
    · simpa [Finset.piecewise,h] using left i
  obtain ⟨legal,paid⟩ := Next.UVStress.root_sum T β rest atField sign (fun i _=>safe i) seam
  rw [same]
  refine ⟨legal,paid.trans ?_⟩
  have each (t : Finset I) (ht : t∈rest) : ‖sign t‖*T.rootTest β (atField t) ≤ δ*∏ i,fee i := by
    have low : t ≠ ∅ := (Finset.mem_erase.mp ht).1
    simpa [sign,atField] using (bought t low).trans (price t low fee nonneg pos small)
  have number : rest.card = (2:ℕ)^Fintype.card I-1 := by simp [rest,Finset.card_erase_of_mem]
  calc
    _ ≤ ∑ _t ∈ rest,δ*∏ i,fee i := Finset.sum_le_sum each
    _ = _ := by simp [number,mul_assoc]

end YM.Integration.WilsonCapturedPrimaryWardMixed
