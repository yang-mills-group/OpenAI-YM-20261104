import YM.Integration.PhysicalForestMarkedRay
/-! Complex charges and finite signed sums on one real physical forest ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalForestSignedJet
open Function Finset PhysicalForestMarkedRay
open scoped Classical BigOperators ContDiff

theorem reading (k:ℕ) (f:ℝ→ℂ) (h:ContDiffAt ℝ k f 0):
    readJet k f=(((k.factorial:ℝ)⁻¹:ℝ):ℂ)*iteratedDeriv k f 0:=by
  have part (L:ℂ→L[ℝ]ℝ):iteratedDeriv k (L ∘ f) 0=L (iteratedDeriv k f 0):=by
    simp only [iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left h le_rfl]
    rfl
  have re:=part Complex.reCLM
  have im:=part Complex.imCLM
  change iteratedDeriv k (Complex.re ∘ f) 0=(iteratedDeriv k f 0).re at re
  change iteratedDeriv k (Complex.im ∘ f) 0=(iteratedDeriv k f 0).im at im
  rw [readJet,re,im]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

theorem roster {I:Type} [Fintype I] (k:ℕ) (f:I→ℝ→ℂ) (c:I→ℂ) (h:∀i,ContDiffAt ℝ k (f i) 0):
    readJet k (fun t=>∑i,c i*f i t)=∑i,c i*readJet k (f i):=by
  classical
  have one (i:I):ContDiffAt ℝ k (fun t=>c i*f i t) 0:=contDiffAt_const.mul (h i)
  rw [reading k _ (ContDiffAt.sum (s:=univ) (fun i _=>one i)),iteratedDeriv_fun_sum (fun i _=>one i),Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [reading k (f i) (h i)]
  have moved:iteratedDeriv k (fun t=>c i*f i t) 0=c i*iteratedDeriv k (f i) 0:=
    iteratedDeriv_fun_const_smul_field (c i) (f i)
  rw [moved];ring

end YM.Integration.WilsonOriginalForestSignedJet
