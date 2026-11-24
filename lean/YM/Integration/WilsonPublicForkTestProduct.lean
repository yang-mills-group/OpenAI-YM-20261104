import YM.Integration.WilsonPublicForkIndependentPlacement

/-! Two separately supported profiles test an ordinary joint kernel.
The finite retained two-point terms factor using the product measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkTestProduct
open Filter Function Set MeasureTheory FVA2.O
open scoped Topology BigOperators Classical
variable {n m:ℕ}{I:Type}[Fintype I]
  (ψ:Test n)(φ:Test m)

abbrev space:=(tsupport ψ)×ˢ(tsupport φ)
def tested (f:Points n×Points m→ℂ):ℂ:=∫p:Points n×Points m,(ψ p.1*φ p.2)*f p
private theorem whole {f:Points n×Points m→ℂ}(c:ContinuousOn f (space ψ φ)):
    Integrable (fun p:Points n×Points m=>(ψ p.1*φ p.2)*f p):=by
  let g:=fun p:Points n×Points m=>(ψ p.1*φ p.2)*f p
  have charged:ContinuousOn g (space ψ φ):=((ψ.continuous.comp continuous_fst).mul
    (φ.continuous.comp continuous_snd)).continuousOn.mul c
  have compact:IsCompact (space ψ φ):=ψ.hasCompactSupport.prod φ.hasCompactSupport
  have rewrite:(space ψ φ).indicator g=g:=by
    funext p
    by_cases yes:p∈space ψ φ
    · exact indicator_of_mem yes _
    rw [indicator_of_notMem yes];change 0=(ψ p.1*φ p.2)*f p
    by_cases x:p.1∈tsupport ψ
    · have y:p.2∉tsupport φ:=fun inφ=>yes ⟨x,inφ⟩
      rw [image_eq_zero_of_notMem_tsupport y];ring
    · rw [image_eq_zero_of_notMem_tsupport x];ring
  have paid:Integrable ((space ψ φ).indicator g):=(charged.integrableOn_compact compact).integrable_indicator compact.measurableSet
  rw [rewrite] at paid;exact paid

theorem factor (a:Points n→ℂ)(b:Points m→ℂ):
    tested ψ φ (fun p=>a p.1*b p.2)=ψ.applyTo a*φ.applyTo b:=by
  have eq:(fun p:Points n×Points m=>(ψ p.1*φ p.2)*(a p.1*b p.2))=
    (fun p:Points n×Points m=>(ψ p.1*a p.1)*(φ p.2*b p.2)):=by funext p;ring
  rw [tested,eq];exact integral_prod_mul (μ:=volume) (ν:=volume) (fun x=>ψ x*a x) (fun z=>φ z*b z)

theorem cut (f:Points n×Points m→ℂ)(a:I→Points n→ℂ)(b:I→Points m→ℂ)
    (fc:ContinuousOn f (space ψ φ))(ac:∀i,ContinuousOn (a i) (tsupport ψ))
    (bc:∀i,ContinuousOn (b i) (tsupport φ)):
    tested ψ φ f-∑i,ψ.applyTo (a i)*φ.applyTo (b i)=tested ψ φ (fun p=>f p-∑i,a i p.1*b i p.2):=by
  have term(i:I):Integrable (fun p:Points n×Points m=>(ψ p.1*φ p.2)*(a i p.1*b i p.2)):=
    whole ψ φ (((ac i).comp continuous_fst.continuousOn (fun _ hi=>hi.1)).mul
      ((bc i).comp continuous_snd.continuousOn (fun _ hi=>hi.2)))
  simp_rw [←factor ψ φ]
  unfold tested;simp only [mul_sub,Finset.mul_sum]
  rw [integral_sub (whole ψ φ fc) (integrable_finsetSum _ (fun i _=>term i)),integral_finsetSum _ (fun i _=>term i)]

theorem mass (f:Points n×Points m→ℂ){B:ℝ}(paid:∀p∈space ψ φ,‖f p‖≤B):
    ‖tested ψ φ f‖≤Read.Value ψ*Read.Value φ*B:=by
  have psi:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have ext:Integrable φ:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have wallet:Integrable (fun p:Points n×Points m=>‖ψ p.1‖*‖φ p.2‖):=psi.norm.mul_prod ext.norm
  unfold tested
  refine (norm_integral_le_of_norm_le (wallet.mul_const B) (Eventually.of_forall ?_)).trans_eq ?_
  · intro p;change ‖(ψ p.1*φ p.2)*f p‖≤(‖ψ p.1‖*‖φ p.2‖)*B;rw [norm_mul,norm_mul]
    by_cases yes:p∈space ψ φ
    · exact mul_le_mul_of_nonneg_left (paid p yes) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    by_cases x:p.1∈tsupport ψ
    · have y:p.2∉tsupport φ:=fun hy=>yes ⟨x,hy⟩
      simp [image_eq_zero_of_notMem_tsupport y]
    · simp [image_eq_zero_of_notMem_tsupport x]
  · rw [integral_mul_const];apply congrArg (fun t:ℝ=>t*B)
    exact integral_prod_mul (μ:=volume) (ν:=volume) (fun x=>‖ψ x‖) (fun z=>‖φ z‖)

end YM.Integration.WilsonPublicForkTestProduct
