import YM.Push.LOCAL_SPLITTING.Leading

/-! Engineering horizontal estimates on one step, retaining both weights inside towers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Lattice Wilson RG Labels Bid Work.G08
open scoped BigOperators
variable {G:Gauge}{D:ℕ}(F:Labels.Frame G D)(e:ℕ)

def cut : F.Coeff →ₗ[ℂ] F.Coeff where
   toFun v i := if (F.grades i).1 ≤ e then v i else 0
   map_add' v w := by ext i; by_cases h:(F.grades i).1 ≤ e <;> simp [h]
   map_smul' v w := by ext i; by_cases h:(F.grades i).1 ≤ e <;> simp [h]
@[simp] lemma cut_at (v:F.Coeff)(i:F.Index) : cut F e v i = if (F.grades i).1 ≤ e then v i else 0 := rfl
@[simp] lemma cut_idem (v:F.Coeff) : cut F e (cut F e v)=cut F e v:= by ext i; by_cases h:(F.grades i).1 ≤ e <;> simp [h]
def shed : F.Coeff→ₗ[ℂ]F.Coeff:= LinearMap.id - cut F e
lemma shed_is (v:F.Coeff) : shed F e v=v - cut F e v:=rfl
@[simp] lemma shed_at (v:F.Coeff)(i:F.Index) : shed F e v i = if (F.grades i).1 ≤ e then 0 else v i := by
   by_cases h:(F.grades i).1 ≤ e <;> simp [shed_is,h]
@[simp] lemma cut_shed (v:F.Coeff) : cut F e (shed F e v)=0:=by rw [shed_is,map_sub,cut_idem,sub_self]
@[simp] lemma shed_cut (v:F.Coeff) : shed F e (cut F e v)=0:=by rw [shed_is,cut_idem,sub_self]
lemma from_shed (v:F.Coeff) : cut F e v+shed F e v=v:=by rw [shed_is]; abel
lemma cut_vowel (L : Side) (v:F.Coeff) : cut F e (vowel F L v)=vowel F L (cut F e v) := by ext i; by_cases h:(F.grades i).1 ≤ e <;> simp [vowel,h]
lemma shed_vowel (L : Side) (v:F.Coeff) : shed F e (vowel F L v)=vowel F L (shed F e v) := by ext i; by_cases h:(F.grades i).1 ≤ e <;> simp [vowel,h]

lemma pair_size (v:F.Coeff) : F.coeffSize v= F.coeffSize (cut F e v) + F.coeffSize (shed F e v):= by
   unfold Frame.coeffSize; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>by by_cases h:(F.grades i).1 ≤ e <;> simp [h]
lemma price_cut (v:F.Coeff) : F.coeffSize (cut F e v) ≤ F.coeffSize v:= (le_add_of_nonneg_right (size_nonneg F _)).trans_eq (pair_size F e v).symm
lemma price_shed (v:F.Coeff) : F.coeffSize (shed F e v) ≤ F.coeffSize v:= (le_add_of_nonneg_left (size_nonneg F _)).trans_eq (pair_size F e v).symm
@[simp] lemma size_zero : F.coeffSize 0=0:=by simp [Frame.coeffSize]
lemma size_sub (v w:F.Coeff) : F.coeffSize (v-w) ≤ F.coeffSize v + F.coeffSize w:= by
   unfold Frame.coeffSize
   rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum (fun i _=> norm_sub_le _ _)

lemma above_size (L : Side) (v:F.Coeff) : F.coeffSize (shed F e (vowel F L v)) ≤ (L.val:ℝ)^(D-(e+1)) * F.coeffSize (shed F e v):= by
   rw [shed_vowel]; unfold Frame.coeffSize; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=> ?_
   simp only [vowel,norm_mul,Complex.norm_pow,Complex.norm_natCast,shed_at]
   split; · simp
   next h => exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast L.property) (by omega)) (norm_nonneg _)
lemma below_size (L : Side) (v:F.Coeff) : (L.val:ℝ)^(D-e) * F.coeffSize (cut F e v) ≤ F.coeffSize (cut F e (vowel F L v)):= by
   rw [cut_vowel]; unfold Frame.coeffSize; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=> ?_
   simp only [vowel,norm_mul,Complex.norm_pow,Complex.norm_natCast,cut_at]
   split
   next h => exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast L.property) (by omega)) (norm_nonneg _)
   simp

variable {T:F.Coeff ≃ₗ[ℂ] F.Coeff}{c:ℝ}
open Push.Local in
lemma above_leading (v:F.Coeff) (h:Leading T.toLinearMap c)(hv:cut F e v=0) : cut F e (T v)=0:=by
   ext i; rw [cut_at]; split
   next hX =>
     change T.toLinearMap v i=0
     rw [← matrix_coeff]; refine Finset.sum_eq_zero fun j _=> ?_
     by_cases ha:(F.grades j).1 ≤ e
     · have hx:v j=0:=by simpa [ha] using congr_fun hv j
       rw [hx,mul_zero]
     have hx:T.toLinearMap (column F j) i=0:=Classical.byContradiction fun H=> ha ((h.triangular i j (by rintro rfl; contradiction) H).le.trans hX)
     rw [hx,zero_mul]
   rfl
open Push.Local in
lemma above_inverse (v:F.Coeff) (h:Leading T.toLinearMap c)(hv:cut F e v=0) : cut F e (T.symm v)=0:=by
   let K:= LinearMap.ker (cut F e); let P := T.toLinearMap.restrict (p:=K) (q:=K) (fun x hx=> above_leading F e _ h hx)
   have hi: Injective P:=by
      intro x y hh; exact Subtype.ext (T.injective (show T x.val=T y.val from congr_arg Subtype.val hh))
   obtain ⟨w,hw⟩:= LinearMap.injective_iff_surjective.mp hi (⟨v,hv⟩:K)
   have he:T w.val=v:=congr_arg Subtype.val hw
   rw [← he,LinearEquiv.symm_apply_apply]; exact w.property
open Push.Local in
lemma inverse_bill (v:F.Coeff) {A:ℝ} (h:Leading T.toLinearMap c) (hv:∀ x,F.coeffSize (T.symm x) ≤ A*F.coeffSize x):
    F.coeffSize (cut F e v) ≤ A*F.coeffSize (cut F e (T v)):=by
    have hx : cut F e (T.symm (cut F e (T v)))=cut F e v:= by
       apply sub_eq_zero.mp
       rw [← map_sub]; have ht:= above_inverse F e (cut F e (T v) - T v) h (by simp)
       rwa [map_sub,LinearEquiv.symm_apply_apply] at ht
    exact hx ▸ le_trans (price_cut F e (T.symm _)) (hv _)
end YM.Frontier6.Canvas
