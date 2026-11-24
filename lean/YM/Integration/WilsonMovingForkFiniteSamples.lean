import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination

/-! Finite samples on the support of one prescribed test. All specified
moments share the same points and the same positive weights. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkFiniteSamples
open Filter Set MeasureTheory Metric
open scoped Classical BigOperators ENNReal

theorem original {A E:Type}[MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
    (μ:Measure A)[IsFiniteMeasure μ](s:Set A)(covered:∀ᵐ a ∂μ,a∈s)(f:A→E)(ok:Integrable f μ)
    {ε:ℝ}(ep:0<ε):
    ∃ι:Type,∃_:Fintype ι,∃x:ι→s,∃w:ι→ℝ,(∀i,0≤w i) ∧ ∑i,w i=μ.real univ ∧
      ‖(∫a,f a ∂μ)-∑i,w i • f (x i)‖≤ε:=by
  by_cases zero:μ=0
  · refine ⟨Fin 0,inferInstance,Fin.elim0,Fin.elim0,(fun j=>Fin.elim0 j),?_⟩
    simpa [zero] using ep.le
  letI : NeZero μ:=⟨zero⟩
  let mass:=μ.real univ
  have pos:0<mass:=measureReal_univ_pos
  have inside:(⨍a,f a ∂μ)∈closure (convexHull ℝ (f '' s)):=by
    apply (convex_convexHull ℝ (f '' s)).closure.average_mem isClosed_closure _ ok
    filter_upwards [covered] with a ha
    exact subset_closure (subset_convexHull ℝ (f '' s) ⟨a,ha,rfl⟩)
  obtain ⟨b,hb,near⟩:=Metric.mem_closure_iff.mp inside (ε/mass) (div_pos ep pos)
  rw [convexHull_eq] at hb
  obtain ⟨ι,t,w,z,nonneg,one,hit,bary⟩:=hb
  choose x hx value using fun i:t=>hit i.val i.property
  refine ⟨t,inferInstance,fun i=>⟨x i,hx i⟩,fun i=>mass*w i.val,fun i=>mul_nonneg pos.le (nonneg i i.property),?_,?_⟩
  · rw [←Finset.mul_sum,Finset.sum_coe_sort,one,mul_one]
  · have sampled:∑i:t,(mass*w i.val) • f (x i)=mass • b:=by
      calc
        _ = ∑i:t,mass • (w i.val • z i.val):=by
          refine Finset.sum_congr rfl fun i _=>?_
          rw [value i,mul_smul]
        _ = mass • ∑i:t,w i.val • z i.val:=(Finset.smul_sum ..).symm
        _ = mass • b:=by
          rw [←bary,Finset.centerMass,one,inv_one,one_smul]
          exact congrArg (mass • ·) (Finset.sum_coe_sort t fun i=>w i • z i)
    change ‖(∫a,f a ∂μ)-∑i:t,(mass*w i.val) • f (x i)‖≤ε
    rw [sampled,←measure_smul_average μ f,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos pos]
    exact (lt_div_iff₀' pos).mp (by simpa [dist_eq_norm] using near) |>.le

end YM.Integration.WilsonMovingForkFiniteSamples
end
