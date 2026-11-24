import YM.Integration.WilsonMaxwellThermometerLower
import YM.Integration.WilsonMaxwellThermometerDifferentiated

/-! The two levels of derivatives allowed by the cap-six two-curvature sector
are spanned on the native solution quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerJetSpan
open Set Function Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerDifferentiated
open scoped BigOperators

def rows : (j : ℕ) → Set (Flavor j)
  | 0 => {p | ∃ s a, p=slot s a}
  | 1 => {p | ∃ s k a, p=firstSlot s k a}
  | 2 => {p | ∃ (s : Bool) (u : E4) (k : Axis) (a : P), p=feed u 1 (firstSlot s k a)}
  | _+3 => ∅

private theorem firsts (W : Submodule ℝ (Flavor 1)) (h : ∀ s k a, firstSlot s k a ∈ W) :
    W = ⊤ := by
  apply top_unique; rw [← shift_span]; apply Submodule.span_le.mpr
  rintro p ⟨i,a,b,_,rfl⟩
  have hg : W.comap (feed (basis i) 0)=⊤ :=
    WilsonMaxwellThermometerLower.generators _ (fun s a => h s i a)
  exact (show cell a b ∈ W.comap (feed (basis i) 0) from hg.ge Submodule.mem_top)

private theorem seconds (W : Submodule ℝ (Flavor 2))
    (h : ∀ s u k a, feed u 1 (firstSlot s k a) ∈ W) : W=⊤ := by
  have hc (u : E4) : W.comap (feed u 1)=⊤ := firsts _ (fun s k a => h s u k a)
  apply top_unique; rw [← unitStay 2]; apply Submodule.span_le.mpr
  rintro t ⟨u,a,b,rfl⟩
  have hq : feed (u 0) 1 (feed (u 1) 0 (cell a b)) ∈ W :=
    (hc (u 0)).ge (Submodule.mem_top : feed (u 1) 0 (cell a b) ∈ (⊤ : Submodule ℝ _))
  have hr : feed (u 0) 1 (feed (u 1) 0 (cell a b)) = (2:ℝ) • stay u a b := by
    apply LinearMap.ext; intro A
    change (feed (u 1) 0 (cell a b)) (lower ℝ 1 (u 0) A) = 2 * A.val a b u
    rw [feeds_first]; change (lower ℝ 1 (u 0) A).val a b (fun _ => u 1) = _
    rw [lower_apply]; norm_num; congr 2; funext i; fin_cases i <;> rfl
  rw [hr] at hq
  simpa [smul_smul] using W.smul_mem (2:ℝ)⁻¹ hq

theorem full (j : ℕ) (hj : j≤2) : Submodule.span ℝ (rows j) = ⊤ := by
  interval_cases j
  · apply WilsonMaxwellThermometerLower.generators
    exact fun s a => Submodule.subset_span ⟨s,a,rfl⟩
  · apply firsts
    exact fun s k a => Submodule.subset_span ⟨s,k,a,rfl⟩
  · apply seconds
    exact fun s u k a => Submodule.subset_span ⟨s,u,k,a,rfl⟩

end YM.Integration.WilsonMaxwellThermometerJetSpan
