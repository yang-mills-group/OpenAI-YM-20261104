import YM.FormalOPE.RG10.Transit.Merits
import YM.FormalOPE.RG10.Transit.Window

/-!
# Price a profile application on tested top stencils at any displayed finite horizon

Use a common compact translated center (can subsequently average over a volume at coarser
stop), arbitrary `α`-indexed profile variables, integrable coefficients included. Might have an
extremely large number of finite terms at given regulator, e.g. transforms before projection,
but center density normalized in testing. These results don't count them when taking the *norm*
of the signed assembly. Field/vertex and Taylor power indices remain exactly the same.
`Finite` presentation plausible for the **top** product and root operation (finite volume
and every field stencil is a fixed test expression on the finite lattice before smearing), not
requiring a finite atomic representation for arbitrary derivative measures used in bounding its
post-capture representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Finset MeasureTheory Filter Function Route Transit
open scoped Topology BigOperators ENNReal Classical
variable {I : Type} {J α : Type*} [MeasurableSpace α] (μ : Measure α)
variable (U : Finset J) (f : J→ Channel I) (g : J → α → ℂ)

def collection (x : α) := ∑ i∈U,g i x • f i
def smeared := ∑ i∈U,(∫ x,g i x ∂μ) • f i

def aboard (p : Channel I) (i : ℕ) (r : Letters I) := MvPolynomial.coeff r (coeff i p)

def box (i : ℕ) := U.biUnion fun j => (coeff i (f j)).support
local notation "ρ" => collection U f g
local notation "τ" => smeared μ U f g

omit [MeasurableSpace α] in
lemma terms (x : α) (i : ℕ) (r : Letters I) : aboard (ρ x) i r = ∑ a∈U,g a x * aboard (f a) i r := by
  unfold aboard collection; simp_rw [map_sum,MvPolynomial.coeff_sum,coeff_smul,MvPolynomial.coeff_smul,smul_eq_mul]
lemma stamp (i : ℕ) (r : Letters I) : aboard τ i r = ∑ a∈U,(∫ x,g a x ∂μ) * aboard (f a) i r := terms U f (fun a (_:Unit)=> (∫ x,g a x ∂μ)) () ..

-- payload fibers
variable (hg : ∀ i∈U, Integrable (g i) μ)
include hg
lemma aboard_pays i r : Integrable (fun x=> aboard (ρ x) i r) μ := by simp_rw [terms]; exact integrable_finsetSum _ fun j hj => (hg j hj).mul_const _
lemma aboard_average (i r) : (∫ x,aboard (ρ x) i r ∂μ) = aboard τ i r:= by
  simp_rw [terms, stamp]; rw [integral_finsetSum];
  · simp_rw [MeasureTheory.integral_mul_const]
  exact fun j hj => (hg j hj).mul_const _
omit hg
variable (i : ℕ)
lemma plays (v : J→ℂ) :
    (coeff i (∑ x∈U,v x • f x)).support ⊆ box U f i := by
  intro r hr; by_contra he; apply MvPolynomial.mem_support_iff.mp hr; rw [map_sum,MvPolynomial.coeff_sum];
  exact sum_eq_zero fun j hj => by rw [coeff_smul,MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.mp (show r∉(coeff i (f j)).support from fun h=>he (mem_biUnion.mpr ⟨_,hj,h⟩)),smul_zero]

lemma box_value (w : I→ℝ) (n : ℕ) (p : Channel I) (he : (coeff i p).support⊆box U f i) :
    worth w n (coeff i p)= ∑ a∈box U f i,fare w n a * ‖aboard p i a‖ := sum_subset he fun j _ hj => by rw [MvPolynomial.notMem_support_iff.mp hj,norm_zero,mul_zero]

include hg
variable (w : I→ℝ) (n r : ℕ)
lemma box_income : Integrable (fun x=>worth w n (coeff i (ρ x))) μ := by
  have hh (x:α) : worth w n (coeff i (ρ x))= ∑ a∈box U f i,fare w n a * ‖aboard (ρ x) i a‖ := box_value U f i w n (ρ x) (plays U f i (fun j=>g j x))
  simp_rw [hh]
  exact integrable_finsetSum _ fun j _ => (aboard_pays μ U f g hg i j).norm.const_mul _

variable (hw : 0 ≤ w)
include hw
lemma averaging : worth w n (coeff i τ) ≤ (∫ x, worth w n (coeff i (ρ x)) ∂μ) := by
  rw [box_value U f i w n τ (plays U f i (fun j=> ∫ x, g j x ∂μ))];
  have hh x: worth w n (coeff i (ρ x))= _ := box_value U f i w n (ρ x) (plays U f i (fun j=>g j x))
  simp_rw [hh, integral_finsetSum _ (fun z _=> (aboard_pays μ U f g hg i z).norm.const_mul _), MeasureTheory.integral_const_mul]
  refine sum_le_sum fun z hz=>?_;
  rw [← aboard_average μ U f g hg]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (fare_pos _ hw _ _).le

lemma applies (φ : α→ℝ) (hf: Integrable φ μ) (h : ∀ᵐ x∂μ,mag w n r (ρ x) ≤ φ x) : mag w n r τ ≤ ∫ x,φ x ∂μ := by
  apply le_trans (b:=∫ x, mag w n r (ρ x) ∂μ) _ (integral_mono_ae (integrable_finsetSum _ fun i _=>box_income μ U f g hg i w n) hf h)
  unfold mag; rw [integral_finsetSum];
  · exact sum_le_sum fun i hi=>averaging μ U f g hg i w n hw
  exact fun i _ => box_income μ U f g hg i w n
omit hw
lemma obeys (F : Submodule ℂ (Channel I)) (h : ∀ᵐ x∂μ, ρ x ∈ F) : τ∈ F := by
  by_contra ht; obtain ⟨q,hq,hq'⟩:= Submodule.exists_dual_map_eq_bot_of_notMem ht inferInstance; apply hq
  have he : (fun x => q (ρ x)) =ᵐ[μ] 0 := by
    filter_upwards [h] with x hx
    have ht : q (ρ x)∈ F.map q:= Submodule.mem_map_of_mem hx; rw [hq'] at ht; exact Submodule.mem_bot ℂ |>.1 ht
  calc
    _ = ∫ x,q (ρ x) ∂μ := by
      unfold smeared collection; simp_rw [map_sum,map_smul]; rw [integral_finsetSum ..];
      · simp_rw [integral_smul_const]
      exact fun j hj => (hg j hj).smul_const _
    _ = _ := by rw [integral_congr_ae he,integral_zero'] -- inspect

private def proper (I : Type) (r d : ℕ) : Submodule ℂ (Channel I) where
  carrier := {a | Guard a r d}
  zero_mem' := Guard.zero
  add_mem' := Guard.add
  smul_mem' c _ h := Guard.const_smul h c
include hg in
lemma stationed (d r : ℕ) (h : ∀ᵐ x∂μ, Guard (ρ x) r d) : Guard τ r d := obeys μ U f g hg (proper I r d) h

end YM.FormalOPE.RG10.Capture
