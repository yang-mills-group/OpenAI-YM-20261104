import YM.Integration.WilsonSeparatedOriginalSlabWatchMass
import YM.Integration.WilsonSeparatedOriginalSlabWatchRaw

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchBilling
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Next.UVStress
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{n h:ℕ}

theorem supported {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](K:Set (Points n))(hk:IsCompact K)
    (q:Points n→V)(live:ContinuousOn q K)(outside:∀y∉K,q y=0):Integrable q volume:=by
  have same:K.indicator q=q:=by funext y;by_cases live:y∈K
                                · simp only [Set.indicator_of_mem live]
                                · rw [Set.indicator_of_notMem live,outside y live]
  rw [←same];exact (live.integrableOn_compact hk).integrable_indicator hk.measurableSet

theorem observed (W:Watch C)(c:ℂ)(K:Set (Points n))(compact:IsCompact K)(e:Points n→ℂ)
    (smooth:Continuous e)(outside:∀y∉K,e y=0)(signal:Points n→ℂ)(q:Points n→S.Field h)
    (physical:ContinuousOn signal K)(fee:ContinuousOn q K)(B:ℝ)(error:∀y,e y≠0→‖signal y-W.tester S h (q y)‖≤B):
    ‖c*(∫y,e y*signal y)-W.tester S h (c • ∫y,e y • q y)‖≤‖c‖*(∫y,‖e y‖)*B:=by
  have test:Integrable e volume:=supported K compact e smooth.continuousOn outside
  have realPart:Integrable (fun y=>e y*signal y) volume:=supported K compact _ (smooth.continuousOn.mul physical) (fun y hy=>by rw [outside y hy,zero_mul])
  have vector:Integrable (fun y=>e y • q y) volume:=supported K compact _ (smooth.continuousOn.smul fee) (fun y hy=>by rw [outside y hy,zero_smul])
  have projected:Integrable (fun y=>e y*W.tester S h (q y)) volume:=supported K compact _ (smooth.continuousOn.mul ((W.tester S h).toContinuousLinearMap.continuous.comp_continuousOn fee)) (fun y hy=>by rw [outside y hy,zero_mul])
  have image:(W.tester S h) (∫y,e y • q y)=∫y,e y*W.tester S h (q y):=by
    calc _=∫y,(W.tester S h).toContinuousLinearMap (e y • q y):=((W.tester S h).toContinuousLinearMap.integral_comp_comm vector).symm
         _=_:=integral_congr_ae (Eventually.of_forall (fun y=>by change (W.tester S h) (e y • q y)=_;rw [map_smul,smul_eq_mul]))
  rw [map_smul,smul_eq_mul,image,←mul_sub,←integral_sub realPart projected,norm_mul]
  rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le (test.norm.mul_const B);apply Eventually.of_forall;intro y
  by_cases nonzero:e y=0
  · simp only [nonzero,zero_mul,sub_self,norm_zero,le_rfl]
  · rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left (error y nonzero) (norm_nonneg _)

end YM.Integration.WilsonSeparatedOriginalSlabWatchBilling
