import YM.Integration.FVA1Physical.Marked.QuayReclosure

/-! A finite test bank is materialized before choosing any field coefficients.
Regular rows retain their basis/channel labels and forced rows are combined
only on the identical signed native host. Its budget uses the l¹ mass of the
test coefficients, never the number of labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Function Finset Lattice RG YM.Wilson Source Labels Extra.Histories LocalLTE.Vinca Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {R : Rep G n} {A : Hol G}
    {J : Type} [Fintype J] (index : ℕ ≃ J × ℕ) (Z Q : J → Coefficient F n)
    (w : J → ℂ) {κ ε : ℝ}

def combine (P : J → Coefficient F n) (z : J → ℂ) : Coefficient F n :=
  merge index fun j=>stretch (z j) (P j)

theorem combine_difference : decrement (combine index Z w) (combine index Q w) =
    combine index (fun j=>decrement (Z j) (Q j)) w := by
  unfold combine merge stretch decrement
  simp only [tsum_fintype,smul_sub,Finset.sum_sub_distrib]
  congr 1
  funext k U
  simp [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]

private theorem account_rem {full pred : Coefficient F n} (a : Account R A full pred κ ε) (hk : 0<κ) :
    (decrement full pred).remBound 0 R κ (2*ε) := by
  obtain ⟨r,f,hr,hf,rb,fb⟩ := a.remainder
  have pos := (Work.G08.size_nonneg F _).trans a.head
  refine ⟨ε, ε, pos, pos, by linarith, hk, ⟨r,rb,hr⟩,f,?_,?_⟩
  · have h := budget_scale hk.le fb
    convert! h using 1
    funext k; unfold BudgetPoint.mass; field_simp [hk.ne']
  · intro i
    have h : (decrement full pred).forced i=full.forced i := by
      change (full.forced-pred.forced) i=_
      rw [a.forced_zero,sub_zero]
    rw [h]; exact hf i

/-- One common support array for all weights. The residual has the exact
physical signed host coefficients and both complete countable native budgets. -/
theorem common_test_budget (hk : 0<κ) (a : ∀ j,Account R A (Z j) (Q j) κ ε) :
    let Z' := combine index Z w
    let Q' := combine index Q w
    let Δ := decrement Z' Q'
    Z'.support=(fun k=>(Z (index k).1).support (index k).2) ∧ Z'.support=Q'.support ∧
      Z'.Format 0 A R ∧ Q'.Format 0 A R ∧ Δ.Format 0 A R ∧
      F.coeffSize Δ.x ≤ (∑ j,‖w j‖)*ε ∧ Δ.remBound 0 R κ (2*(∑ j,‖w j‖)*ε) ∧
      ∀ (k : ℕ) (V : Config G n), Δ.forced k V=∑ j,w j * (Z j).forced k V := by
  intro Z' Q' Δ
  have hd : Δ=combine index (fun j=>decrement (Z j) (Q j)) w := combine_difference index Z Q w
  have hc (j:J) := stretch_rem (w j) (account_rem (a j) hk)
  refine ⟨rfl,?_,merge_format _ _ (fun j=>stretch_format _ (a j).full_format),
    merge_format _ _ (fun j=>stretch_format _ (a j).predicted_format),?_,?_,?_,?_⟩
  · funext k
    exact congrFun (a (index k).1).alignment (index k).2
  · rw [hd]; exact merge_format _ _ (fun j=>stretch_format _ (a j).lawful)
  · rw [hd]; change F.coeffSize (∑' j,w j • (decrement (Z j) (Q j)).x) ≤ _
    rw [tsum_fintype,Finset.sum_mul]
    refine (Size.finite F _ _).trans (sum_le_sum fun j _=>?_)
    rw [Size.smul]; exact mul_le_mul_of_nonneg_left (a j).head (norm_nonneg _)
  · rw [hd]
    have h := (merge_budget index _ hk hc (hasSum_fintype _).summable).1
    have cost : (∑' j,‖w j‖*(2*ε))=2*(∑ j,‖w j‖)*ε := by rw [tsum_fintype,←Finset.sum_mul]; ring
    rw [←cost]; exact h
  · intro k U
    change (∑' j,w j * (Z j).forced k U) - (∑' j,w j * (Q j).forced k U) = _
    simp only [tsum_fintype, (a _).forced_zero,Pi.zero_apply,mul_zero,sum_const_zero,sub_zero]

end YM.Integration.FVA1Physical.Marked.Quay
