import YM.XSpace.VertexTaylor
import YM.AnalyticNext.CUBIC_MATCH.Rays

/-!
# Composing Taylor rules on a fixed finite lattice
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Taylor
open Function MvPolynomial Set Filter
open scoped Topology BigOperators ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  {f g : E → ℂ}

lemma expand_coeff (f : E → ℂ) (n : ℕ) : PowerSeries.coeff n (expandTaylor b f)=divided b n f:= PowerSeries.coeff_mk ..
lemma line_coeff (n : ℕ) (x : E) (hf : ContDiffAt ℝ (↑n) f 0) :
    evalAt b x (PowerSeries.coeff n (expandTaylor b f)) = (n.factorial : ℂ)⁻¹ *iteratedDeriv n (fun t : ℝ=>f (t • x)) 0 := by
  rw [expand_coeff,divided_eval]; apply congr_arg
  let L:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  have ht : L (1:ℝ)=x := one_smul _ _
  unfold iteratedDeriv; rw [show (fun t:ℝ => f (t • x))= f ∘ L from rfl, CubicMatch.jet_comp_linear L (show ContDiffAt ℝ ↑n f (L 0) by rw [map_zero]; exact hf), map_zero]; simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,ht]
private lemma lines {f : E → ℂ} (x : E) (n : ℕ) (hf : ContDiffAt ℝ ω f 0) : ContDiffAt ℝ ↑n (fun t : ℝ => f (t • x)) 0:=by
  let L:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  exact ContDiffAt.comp (f:=L) (0:ℝ) (show ContDiffAt ℝ (↑n) f (L 0) by rw [map_zero]; exact hf.of_le le_top) L.contDiff.contDiffAt

lemma expand_add (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    expandTaylor b (f+g)=expandTaylor b f+expandTaylor b g:=PowerSeries.ext fun n=> from_real b _ _ fun x=>by
  rw [map_add,map_add,line_coeff b (f:=f+g) _ _ ((hf.add hg).of_le le_top),line_coeff b _ _ (hf.of_le le_top),line_coeff b _ _ (hg.of_le le_top)]
  simp only [Pi.add_apply]; rw [iteratedDeriv_fun_add (lines x n hf) (lines x n hg)]; ring
lemma expand_mul (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) :
    expandTaylor b (f*g)=expandTaylor b f*expandTaylor b g := PowerSeries.ext fun n => from_real b _ _ fun x=>by
  rw [line_coeff b (f:=f*g) n x ((hf.mul hg).of_le le_top),PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Pi.mul_apply]; rw [iteratedDeriv_fun_mul (lines x n hf) (lines x n hg),map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [map_mul,line_coeff b _ x (hf.of_le le_top),line_coeff b _ x (hg.of_le le_top), Nat.cast_choose _ (by simpa using hi)]
  field_simp [Nat.factorial_ne_zero]
lemma expand_const (z : ℂ) : expandTaylor b (fun _ => z)=PowerSeries.C (MvPolynomial.C z) := PowerSeries.ext fun n=> from_real b _ _ fun x=>by
  rw [line_coeff b _ _ contDiffAt_const, PowerSeries.coeff_C]; split_ifs with h <;> simp [h,evalAt,iteratedDeriv_const]
end YM.XSpace.Taylor
