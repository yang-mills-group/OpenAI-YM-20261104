import YM.Integration.WilsonMovingForkFiniteSamples
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Signed cubature for a finite family of observations on one prescribed
profile, with its actual total variation and unchanged support. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSignedSamples
open Filter Finset Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem original {A I:Type}[MeasurableSpace A][Fintype I](μ:Measure A)[IsFiniteMeasure μ]
    (s:Set A)(covered:∀ᵐa ∂μ,a∈s)(density:A→ℂ)(row:A→(I→ℂ))
    (variation:Integrable (fun a=>‖density a‖) μ)(moments:Integrable (fun a=>density a • row a) μ)
    {ε:ℝ}(ep:0<ε):∃ι:Type,∃_:Fintype ι,∃x:ι→s,∃ν:ι→ℂ,
      ∑i,‖ν i‖≤(∫a,‖density a‖ ∂μ)+ε ∧
      ‖(∫a,density a • row a ∂μ)-∑i,ν i • row (x i)‖≤ε:=by
  obtain ⟨ι,fi,x,v,positive,_,close⟩:=WilsonMovingForkFiniteSamples.original μ s covered
    (fun a=>(‖density a‖,density a • row a)) (variation.prodMk moments) ep
  let ν:ι→ℂ:=fun i=>(v i:ℂ)*density (x i)
  refine ⟨ι,fi,x,ν,?_⟩
  have weight(i:ι):‖ν i‖=v i*‖density (x i)‖:=by
    simp only [ν,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive i)]
  have split:∑i,v i • (‖density (x i)‖,density (x i) • row (x i))=
      (∑i,‖ν i‖,∑i,ν i • row (x i)):=by
    rw [prod_mk_sum]
    refine Finset.sum_congr rfl fun i _=>Prod.ext ?_ ?_
    · exact (weight i).symm
    · funext k
      change (v i:ℂ)*(density (x i)*(row (x i) k))=((v i:ℂ)*density (x i))*(row (x i) k)
      ring
  rw [integral_pair variation moments,split] at close
  have left:|(∫a,‖density a‖ ∂μ)-∑i,‖ν i‖|≤ε:=(norm_fst_le _).trans close
  exact ⟨by linarith only [(abs_le.mp left).1],(norm_snd_le _).trans close⟩

end YM.Integration.WilsonMovingForkSignedSamples
end
