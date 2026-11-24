import YM.Integration.WilsonOriginalFourierBoxIntegral

/-! Continuous descent of the original localized field across every face
of the period box. The cutoff kills both representatives of each seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactTorusChart
open Set Function AddCircle UnitAddTorus
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalGevreyCutoffDisc (leaf)

def gate {d : ℕ} (a : Fin d → ℝ) (X : (i:Fin d) → Icc (a i) (a i+1)) :
    UnitAddTorus (Fin d) := fun i => ((X i).val : UnitAddCircle)

theorem quotient {d : ℕ} (a : Fin d → ℝ) : Topology.IsQuotientMap (gate a) := by
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro z
    let q (i : Fin d) := AddCircle.equivIoc (1:ℝ) (a i) (z i)
    use fun i => ⟨(q i).val,(q i).property.1.le,(q i).property.2⟩
    ext i
    exact AddCircle.coe_equivIoc
  · fun_prop [gate]

theorem original {d : ℕ} (a l h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ)
    (left : ∀ i, a i ≤ l i) (right : ∀ i, h i ≤ a i+1)
    (sf : ContinuousOn f {x | ∀ i, x i ∈ Icc (a i) (a i+1)}) :
    Continuous (localize a l h f) := by
  apply (quotient a).continuous_iff.mpr
  let unbox (X : (i : Fin d) → Icc (a i) (a i+1)) := fun i => (X i).val
  have real_chart : Continuous unbox := by dsimp [unbox];fun_prop
  have sub : Continuous (f ∘ unbox) :=
    sf.comp_continuous real_chart (fun X i => (X i).property)
  have col : Continuous (fun X : (i : Fin d) → Icc (a i) (a i+1) =>
      (∏ i,window (l i) (h i) ((X i).val))*f (unbox X)) := by
    apply Continuous.mul _ sub
    apply continuous_finsetProd
    intro i _
    exact (WilsonOriginalFiledBoxWindow.smooth (l i) (h i) (n:=0)).continuous.comp
      (continuous_subtype_val.comp (continuous_apply i))
  apply col.congr
  intro X
  by_cases proper : ∀ i, a i < (X i).val
  · have chart (i : Fin d) : (AddCircle.equivIoc (1:ℝ) (a i) (gate a X i)).val = (X i).val :=
      AddCircle.equivIoc_coe_of_mem ⟨proper i,(X i).property.2⟩
    simp [localize,chart,unbox]
  · obtain ⟨i,hi⟩ := not_forall.mp proper
    have eq : (X i).val = a i := le_antisymm (not_lt.mp hi) (X i).property.1
    have endpoint : (AddCircle.equivIoc (1:ℝ) (a i) (gate a X i)).val = a i+1 := by
      have e : gate a X i = ((a i+1:ℝ) : UnitAddCircle) := by simp [gate,eq]
      rw [e]
      exact AddCircle.equivIoc_coe_of_mem ⟨by linarith,le_rfl⟩
    have z₁ : window (l i) (h i) ((X i).val) = 0 := by
      simp [window,leaf,eq,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (left i))]
    have z₂ : window (l i) (h i) ((AddCircle.equivIoc (1:ℝ) (a i) (gate a X i)).val) = 0 := by
      rw [endpoint]
      simp [window,leaf,expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr (right i))]
    simp only [Function.comp_apply,localize]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₁,Finset.prod_eq_zero (Finset.mem_univ i) z₂,zero_mul,zero_mul]

end YM.Integration.WilsonOriginalCompactTorusChart
