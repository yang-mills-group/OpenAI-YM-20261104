import YM.Integration.WilsonCapturedPrimaryDecoder

/-! Recover the rough section fee from the independent nonconstant field
and the original regular remainder. The true captured head is an unknown. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCoreBill
open Finset Labels Lattice RG Source Wilson Push.Local Next.Foundations Trace.Physical.Germ
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d) (A : Hol G)
variable {n : Side} {K : RG.Rep G n} {o : Site n} {q : Coefficient F n} {κ s : ℝ}

def wrapFee : ℝ := (F.extra+1:ℕ)*(germ_close F A).choose

lemma core_difference (x y : F.Coeff) : F.coeffSize (F.core x) ≤ F.coeffSize (F.core y)+F.coeffSize (x-y) := by
  simp only [Labels.Frame.coeffSize,←sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  by_cases eq : i=0
  · simp [Labels.Frame.core,eq]
  · have id : x i=(y i+(x i-y i)) := by ring
    simp only [Labels.Frame.core,LinearMap.coe_mk,AddHom.coe_mk,Function.update_of_ne eq,Pi.sub_apply]
    exact (congrArg norm id).le.trans (norm_add_le _ _)

theorem head (read : q.Format o A K) (rem : q.remBound o K κ s) (order : d ≤ K.p.order)
    (power : d ≤ K.p.power) (cold : wraps K.p n ≤ 1) (z : F.Coeff) :
    F.coeffSize (F.core q.x) ≤ F.coeffSize (F.core z)+F.coeffSize (projection F A K.p.threshold o q-z)+wrapFee F A*s := by
  have wrapped := (germ_close F A).choose_spec.2 K q read rem order power
  have rate := (germ_close F A).choose_spec.1.le
  have sp : 0 ≤ s := by
    obtain ⟨u,v,hu,hv,h,_⟩ := rem
    linarith only [hu,hv,h]
  let x := projection F A K.p.threshold o q
  have cost : F.coeffSize (q.x-x) ≤ wrapFee F A*s := calc
    _ ≤ (F.extra+1:ℕ)*‖q.x-x‖ := size_le_norm F _
    _ = (F.extra+1:ℕ)*‖x-q.x‖ := by rw [norm_sub_rev]
    _ ≤ (F.extra+1:ℕ)*((germ_close F A).choose*wraps K.p n*s) :=
      mul_le_mul_of_nonneg_left wrapped (Nat.cast_nonneg _)
    _ ≤ (F.extra+1:ℕ)*((germ_close F A).choose*s) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right rate cold) sp) (Nat.cast_nonneg _)
    _ = wrapFee F A*s := by unfold wrapFee;ring
  exact (core_difference F q.x x).trans (add_le_add (core_difference F x z) cost)

/-- Retain the scalar in the error and charge only the independent core in
the fee for derivatives on the original section. -/
theorem paid (read : q.Format o A K) (rem : q.remBound o K κ s) (order : d ≤ K.p.order)
    (power : d ≤ K.p.power) (cold : wraps K.p n ≤ 1) (z : F.Coeff) {w t a : ℝ}
    (wp : 0 ≤ w) (tp : 0 ≤ t) (ap : 0 ≤ a)
    (small : t*w ≤ 1/2)
    (heard : ∀ C : ℝ, a ≤ C → w*F.coeffSize (F.core q.x)+s ≤ C →
      F.coeffSize (projection F A K.p.threshold o q-z) ≤ t*C) :
    F.coeffSize (projection F A K.p.threshold o q-z) ≤ 2*t*(a+w*(F.coeffSize (F.core z)+wrapFee F A*s)+s) := by
  let x := projection F A K.p.threshold o q
  let e := F.coeffSize (x-z)
  have sp : 0 ≤ s := by obtain ⟨u,v,hu,hv,h,_⟩ := rem;linarith only [hu,hv,h]
  have corePos : 0 ≤ F.coeffSize (F.core q.x) := sum_nonneg fun _ _ => norm_nonneg _
  have eps : 0 ≤ e := sum_nonneg fun _ _ => norm_nonneg _
  have tested := heard (a+(w*F.coeffSize (F.core q.x)+s))
    (le_add_of_nonneg_right (add_nonneg (mul_nonneg wp corePos) sp)) (le_add_of_nonneg_left ap)
  have physical := head F A read rem order power cold z
  have correction := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left physical wp) tp
  have absorb := mul_le_mul_of_nonneg_right small eps
  change e ≤ _
  change e ≤ _ at tested
  change _ ≤ _*(w*(_+e+_)) at correction
  nlinarith only [tested,correction,absorb]

end YM.Integration.WilsonCapturedPrimaryCoreBill
