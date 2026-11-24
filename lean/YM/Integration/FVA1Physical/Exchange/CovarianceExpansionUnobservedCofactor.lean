import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionOriginalSingletonStock

/-! Keep the old exterior as an arbitrary joint reading. Center it inside
the genuine, possibly null, finite detector bins of the original law.
The centered cofactor annihilates every function of those same bins
before any absolute value is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Set Finset MeasureTheory
open scoped Classical BigOperators
variable {Ω I:Type*}[MeasurableSpace Ω][Fintype I][MeasurableSpace I][MeasurableSingletonClass I]
  (μ:Measure Ω)[IsFiniteMeasure μ](k:Ω→I)(km:Measurable k)

def oldMean (H:Ω→ℂ)(i:I):ℂ:=binMean μ {z|k z=i} H

def unseenOld (H:Ω→ℂ)(z:Ω):ℂ:=H z-oldMean μ k H (k z)

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
theorem old_mean_cap (H:Ω→ℂ)(K:ℝ)(kp:0≤K)(cap:∀z,‖H z‖≤K)(i:I):‖oldMean μ k H i‖≤K:=by
  let B:Set Ω:={z|k z=i}
  let p:=μ.real B
  change ‖(∫z in B,H z ∂μ)/(p:ℂ)‖≤K
  by_cases hz:p=0
  · simpa only [hz,Complex.ofReal_zero,div_zero,norm_zero] using kp
  have pp:0<p:=lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg pp.le,div_le_iff₀ pp]
  have bound:=norm_integral_le_of_norm_le (μ:=μ.restrict B) (integrable_const K) (.of_forall cap)
  exact bound.trans_eq (by rw [setIntegral_const];change p*K=K*p;ring)

include km

theorem unseen_old_integrable (H:Ω→ℂ)(hi:Integrable H μ):
    Integrable (unseenOld μ k H) μ:=by
  let c:=fun z=>oldMean μ k H (k z)
  have cm:Measurable c:=(measurable_of_countable (f:=oldMean μ k H)).comp km
  have cb(z):‖c z‖≤∑i:I,‖oldMean μ k H i‖:=single_le_sum (fun i _=>norm_nonneg (oldMean μ k H i)) (mem_univ (k z))
  exact hi.sub (Integrable.of_bound cm.aestronglyMeasurable _ (.of_forall cb))

theorem unseen_old_bin_zero (H:Ω→ℂ)(hi:Integrable H μ)(i:I):
    ∫z in {z|k z=i},unseenOld μ k H z ∂μ=0:=by
  let B:Set Ω:={z|k z=i}
  let p:=μ.real B
  have bm:MeasurableSet B:=measurableSet_eq_fun km measurable_const
  by_cases hz:p=0
  · have zero:μ B=0:=(measureReal_eq_zero_iff (measure_ne_top μ B)).mp hz
    exact setIntegral_measure_zero _ zero
  have nz:(p:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hz
  change (∫z in B,unseenOld μ k H z ∂μ)=0
  calc _=∫z in B,H z-oldMean μ k H i ∂μ:=integral_congr_ae ((ae_restrict_iff' bm).2 (.of_forall (fun z h=>by
            change H z-oldMean μ k H (k z)=_;rw [show k z=i from h])))
       _=0:=by
         rw [integral_sub hi.integrableOn (integrable_const _),setIntegral_const]
         change (∫z in B,H z ∂μ)-(p:ℂ)*((∫z in B,H z ∂μ)/(p:ℂ))=0
         field_simp [nz]
         ring

theorem unseen_old_finite_test (H:Ω→ℂ)(hi:Integrable H μ)(read:I→ℂ):
    Integrable (fun z=>unseenOld μ k H z*read (k z)) μ ∧
      ∫z,unseenOld μ k H z*read (k z) ∂μ=0:=by
  let B:=fun i:I=>({z:Ω|k z=i}:Set Ω)
  let c:=unseenOld μ k H
  let f:=fun i:I=>(B i).indicator (fun z=>c z*read i)
  have bm(i:I):MeasurableSet (B i):=measurableSet_eq_fun km measurable_const
  have ci:Integrable c μ:=unseen_old_integrable μ k km H hi
  have fi(i:I):Integrable (f i) μ:=(ci.mul_const _).indicator (bm i)
  have eq(z:Ω):(∑i:I,f i z)=c z*read (k z):=by
    rw [sum_eq_single (k z)]
    · exact Set.indicator_of_mem (show z∈B (k z) from rfl) _
    · intro i _ hn
      exact Set.indicator_of_notMem (show z∉B i from fun h=>hn (Eq.symm h)) _
    simp
  have rewrite:(fun z=>unseenOld μ k H z*read (k z))=fun z=>∑i:I,f i z:=funext fun z=>(eq z).symm
  rw [rewrite]
  refine ⟨integrable_finsetSum _ (fun i _=>fi i),?_⟩
  rw [integral_finsetSum _ (fun i _=>fi i)]
  apply sum_eq_zero
  intro i _
  change (∫z,(B i).indicator (fun z=>c z*read i) z ∂μ)=0
  rw [integral_indicator (bm i),integral_mul_const,show (∫z in B i,c z ∂μ)=0 from unseen_old_bin_zero μ k km H hi i,zero_mul]

end YM.Integration.FVA1Physical.Exchange.RoseCut
