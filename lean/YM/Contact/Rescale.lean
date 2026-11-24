import YM.Contact.Trial
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
open Function Set MeasureTheory SeminormFamily
open scoped Topology ContDiff Pointwise BigOperators
namespace YM.Contacts
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull back with the normal-density cancellation factor. -/
def shrink (r:ℝ) (φ:E→ℂ) : E→ℂ := (r^Module.finrank ℝ E)⁻¹ • (fun y=>φ (r⁻¹ • y))
lemma shrink_apply (r:ℝ) (φ:E→ℂ) (y:E) : shrink r φ y=(r^Module.finrank ℝ E)⁻¹ • φ (r⁻¹ • y):=rfl
lemma shrink_support (r:ℝ) (hr:r≠0) (φ:E→ℂ) : support (shrink r φ)⊆(r • support φ) :=
    fun y hy=> ⟨r⁻¹ • y,fun h=> hy (by rw [shrink_apply,h,smul_zero]),smul_inv_smul₀ hr _⟩
variable [FiniteDimensional ℝ E]
lemma shrink_compact (r:ℝ) (φ:Trial E) : HasCompactSupport (shrink r φ):=by
  by_cases hr:r=0
  · by_cases ht:Module.finrank ℝ E=0
    · unfold shrink; simp_rw [ht,pow_zero,inv_one]; rw [one_smul,hr,inv_zero]
      have _ : Subsingleton E:=Module.finrank_zero_iff.mp ht
      exact (Set.toFinite _).isCompact
    simp [shrink,ht,hr, HasCompactSupport.zero]
  have hf:HasCompactSupport (fun y=>φ (r⁻¹ • y)):=by
    refine (φ.hasCompactSupport.smul r).of_isClosed_subset (isClosed_tsupport _) ?_
    intro x hx
    have hs:= tsupport_comp_subset_preimage (φ:E→ℂ) ((continuous_const_smul r⁻¹).comp continuous_id) hx
    exact ⟨r⁻¹ • x,hs,smul_inv_smul₀ hr _⟩
  exact hf.smul_left

omit [FiniteDimensional ℝ E] in
lemma shrink_smooth (r:ℝ) (φ:Trial E):ContDiff ℝ (⊤:ℕ∞) (shrink r φ):=
   (φ.contDiff.comp ((contDiff_const (c:=r⁻¹)).smul contDiff_id)).const_smul (r^Module.finrank ℝ E)⁻¹

def shrinking (r:ℝ) : Trial E→ₗ[ℂ] Trial E where
  toFun φ:= ⟨shrink r φ,shrink_smooth _ _,shrink_compact _ _,fun _ _=>True.intro⟩
  map_add' φ ψ:= by ext1 x; change (r^Module.finrank ℝ E)⁻¹ • (φ (r⁻¹ • x)+ψ (r⁻¹•x))=_; exact smul_add ..
  map_smul' c φ:=by ext1 x; exact smul_comm (r^Module.finrank ℝ E)⁻¹ c (φ (r⁻¹ • x))
lemma shrinking_apply (r:ℝ) (φ:Trial E) (x:E): shrinking r φ x=shrink r φ x:=rfl
lemma shrinking_fun (r:ℝ) (φ:Trial E): (⇑(shrinking r φ))=shrink r φ:=rfl
lemma shrinking_major {r:ℝ}(hr:0<r){j:ℕ} {φ:Trial E} {B:ℝ} (h:Major j φ B):
    Major j (shrinking r φ) ((r^Module.finrank ℝ E)⁻¹ * (max 1 r⁻¹)^j * B):=by
  intro i hi x
  have hs' : ContDiffAt ℝ i (fun x':E=>φ (r⁻¹ • x')) x := ((φ.orders _).comp (contDiff_const.smul contDiff_id)).contDiffAt
  rw [shrinking_fun,shrink, iteratedFDeriv_const_smul_apply hs',iteratedFDeriv_comp_const_smul _ (φ.orders i),norm_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr (pow_pos hr _)).le,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hr).le _),mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul ((pow_le_pow_left₀ (inv_pos.mpr hr).le (le_max_right ..) i).trans (pow_le_pow_right₀ (le_max_left ..) hi)) (h i hi _) (norm_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left ..)) _)) (inv_pos.mpr (pow_pos hr _)).le

omit [FiniteDimensional ℝ E] in
lemma jet_shrink (r:ℝ) {φ:Trial E} (n:ℕ) (x y:E):
    jet n (shrink r φ) x y=(r^Module.finrank ℝ E)⁻¹ • jet n φ (r⁻¹ • x) (r⁻¹ • y):=by
  have hs' : ContDiffAt ℝ n (fun x':E=>φ (r⁻¹ • x')) x := ((φ.orders _).comp (contDiff_const.smul contDiff_id)).contDiffAt
  rw [jet,shrink, iteratedFDeriv_const_smul_apply hs',iteratedFDeriv_comp_const_smul _ (φ.orders n)]
  simp only [jet,smul_apply,←smul_sub,ContinuousMultilinearMap.map_smul_univ]; simp; apply mul_left_comm

omit [FiniteDimensional ℝ E] in
lemma remainder_shrink (r : ℝ) (φ : Trial E) (m:ℤ) : remainder r m (shrink r φ) = shrink r (remainder 1 m φ):=by
  funext y
  change ((_ :ℂ) - _) = (_:ℝ) • ((_ :ℂ) - _);rw [smul_sub]; congr 1
  unfold taylorCut; split_ifs
  · rw [chi_len r, polynomial,polynomial]; simp_rw [jet_shrink, smul_zero, Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _ => smul_comm ..
  · rw [smul_zero]

section
variable [MeasureSpace E] [BorelSpace E] [hH:(volume:Measure E).IsAddHaarMeasure]
include hH
lemma integral_shrink (r:ℝ) (hr:0<r) (φ:E→ℂ): ∫ x,shrink r φ x = ∫ x,φ x:=by
   simp only [shrink,Pi.smul_apply,integral_smul,Measure.integral_comp_inv_smul_of_nonneg _ φ hr.le, inv_smul_smul₀ (pow_pos hr _|>.ne')]
lemma integrable_shrink {r:ℝ} (hr:0<r) {φ:E→ℂ} (h:Integrable φ) : Integrable (shrink r φ):=
    (integrable_comp_smul_iff volume φ (inv_pos.mpr hr).ne').mpr h |>.smul _
end

end YM.Contacts
