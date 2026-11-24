import YM.Integration.WilsonThermometerWeakSpatialTaylor

/-! A signed continuum test controls the point value with two explicit expenses:
the external test derivatives and the Taylor remainder after all of the purchased
joint moments have canceled. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMomentPoint
open Set MeasureTheory Spec Filter Function
open WilsonThermometerWeakSpatialTaylor WilsonThermometerWeakJointMoments
open WilsonThermometerWeakProbeTest
open scoped Classical BigOperators Topology ContDiff
variable {n:ℕ}

private theorem term (F:Points n→ℂ)(z:Points n)(h:ℝ)(k:ℕ):
    Continuous (fun y=>((k.factorial:ℝ)⁻¹*h^k) • iteratedFDeriv ℝ k F z (fun _=>y)):=
  by
    have H : Continuous (fun y:Points n=>iteratedFDeriv ℝ k F z (fun _=>y)):=
      (iteratedFDeriv ℝ k F z).cont.comp (show Continuous (fun y:Points n=>(fun _ : Fin k=>y)) from continuous_pi (fun _=>continuous_id))
    exact H.const_smul ((k.factorial:ℝ)⁻¹*h^k)

theorem exact (f:Test n){M:ℕ}(one:mass f=1)(cancel:Moments f M)(F:Points n→ℂ)(z:Points n)(h:ℝ):
    f.applyTo (polynomial F z h M)=F z:=by
  have each (k:ℕ)(used:k∈Finset.range (M+1)) (nz:k≠0):
      f.applyTo (fun y=>((k.factorial:ℝ)⁻¹*h^k) • iteratedFDeriv ℝ k F z (fun _=>y))=0:=by
    have paid:=cancel k (Nat.pos_of_ne_zero nz) (Nat.le_of_lt_succ (Finset.mem_range.mp used)) (iteratedFDeriv ℝ k F z)
    unfold Test.applyTo at *
    simp_rw [Complex.real_smul,mul_left_comm (f _) ((↑((k.factorial:ℝ)⁻¹*h^k)):ℂ)]
    rw [integral_const_mul,paid,mul_zero]
  unfold Test.applyTo at *
  simp_rw [polynomial,Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _=>f.smearing (term F z h k).continuousOn)]
  rw [Finset.sum_eq_single 0 (fun k used nz=>each k used nz) (by simp)]
  have m:∫x:Points n,f x=1:=by simpa [mass,Test.applyTo] using one
  simp [integral_mul_const,m]

theorem bias (f:Test n){M:ℕ}(one:mass f=1)(cancel:Moments f M)
    {U:Set (Points n)}(openU:IsOpen U)(F:Points n→ℂ)(smooth:ContDiffOn ℝ ∞ F U)
    (z:Points n){h:ℝ}(pos:0<h)(sweep:∀y∈tsupport f,∀t∈Icc (0:ℝ) h,z+t • y∈U)
    {B R:ℝ}(bn:0≤B)(_rn:0≤R)(radius:∀y∈tsupport f,‖y‖≤R)
    (jet:∀y∈tsupport f,∀t∈Icc (0:ℝ) h,‖iteratedFDeriv ℝ (M+1) F (z+t • y)‖≤B):
    ‖f.applyTo (fun y=>F (z+h • y))-F z‖≤
      (∫y,‖f y‖)*(B*R^(M+1)*h^(M+1)/(M.factorial:ℝ)):=by
  let P:=polynomial F z h M
  let cost:=B*R^(M+1)*h^(M+1)/(M.factorial:ℝ)
  have err (y)(hy:y∈tsupport f):‖F (z+h • y)-P y‖≤cost:=
    (remainder F openU smooth M pos (sweep y hy) (jet y hy)).trans (by
      dsimp only [cost];gcongr; exact radius y hy)
  have whole:Continuous (fun y=>f y*F (z+h • y)):=by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy:y∈tsupport f
    · have atF:ContinuousAt F (z+h • y):=(smooth _ (sweep _ hy _ (right_mem_Icc.mpr pos.le))).continuousWithinAt.continuousAt
        (openU.mem_nhds (sweep _ hy _ (right_mem_Icc.mpr pos.le)))
      have move:ContinuousAt (F ∘ (fun u : Points n=>z+h • u)) y:=ContinuousAt.comp (f:=fun u:Points n=>z+h • u) (x:=y) atF (show Continuous (fun u : Points n=>z+h • u) by fun_prop).continuousAt
      exact f.continuous.continuousAt.mul move
    · refine continuousAt_const.congr (?_ : (fun _ => (0:ℂ)) =ᶠ[𝓝 y] fun u => f u*F (z+h • u))
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with u hu
      simp [show f u=0 from hu]
  have ip:Integrable (fun y=>f y*P y):=f.smearing ((continuous_finsetSum _ fun k _=>term F z h k).continuousOn)
  have iF:Integrable (fun y=>f y*F (z+h • y)):=whole.integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  rw [←exact f one cancel F z h,Test.applyTo,Test.applyTo,←integral_sub iF ip]
  refine (norm_integral_le_integral_norm _).trans ?_
  change _≤(∫y,‖f y‖)*cost
  rw [←integral_mul_const]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _)
    ((f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.mul_const cost)
    (Eventually.of_forall fun y=>by
      change ‖f y*F (z+h • y)-f y*P y‖≤‖f y‖*cost
      rw [←mul_sub,norm_mul]
      by_cases hy:y∈tsupport f
      · exact mul_le_mul_of_nonneg_left (err y hy) (norm_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hy])

end YM.Integration.WilsonThermometerWeakMomentPoint
end
