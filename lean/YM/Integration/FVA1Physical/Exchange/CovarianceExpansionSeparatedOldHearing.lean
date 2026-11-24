import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionUnobservedCofactor

/-! An arbitrary correlated bounded exterior stays on the same law. On each
original measuring cell its conditional mean is a permissible finite reading;
only its *centered* correlation with the true complete old field is left.
There is no number-of-cells loss in the quoted price. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory
open scoped Classical BigOperators
variable {Ω I:Type*}[MeasurableSpace Ω][Fintype I][MeasurableSpace I][MeasurableSingletonClass I]
  (μ:Measure Ω)[IsFiniteMeasure μ](k:Ω→I)(km:Measurable k)

include km

theorem original_binned_old_hearing (H:Ω→ℂ)(hi:Integrable H μ)(K:ℝ)(kp:0≤K)(hb:∀z,‖H z‖≤K)
    (g q:Ω→ℂ)(gi:Integrable g μ)(qm:Measurable q)(M:ℝ)(qb:∀z,‖q z‖≤M)
    (read:I→ℂ)(h:ℝ)(mesh:∀z,‖q z-read (k z)‖≤h)(ε:ℝ)
    (localPrice:∀F:I→ℂ,(∀i,‖F i‖≤K) →
      ‖∫z,F (k z)*(g z-q z) ∂μ‖≤ε):
    let old:=unseenOld μ k H
    Integrable (fun z=>old z*g z) μ ∧
      ‖(∫z,H z*(g z-q z) ∂μ)-(∫z,old z*g z ∂μ)‖≤
        ε+(2*K*h)*μ.real univ:=by
  intro old
  let c:=fun z=>oldMean μ k H (k z)
  have cm:Measurable c:=(measurable_of_countable (f:=oldMean μ k H)).comp km
  have cb(i:I):‖oldMean μ k H i‖≤K:=old_mean_cap μ k H K kp hb i
  have ui:Integrable old μ:=unseen_old_integrable μ k km H hi
  have ub(z):‖old z‖≤2*K:=(norm_sub_le ..).trans ((add_le_add (hb z) (cb (k z))).trans_eq (two_mul K).symm)
  have qi:Integrable q μ:=Integrable.of_bound qm.aestronglyMeasurable M (.of_forall qb)
  have rI:Integrable (fun z=>c z*(g z-q z)) μ:=(gi.sub qi).bdd_mul cm.aestronglyMeasurable (.of_forall fun z=>cb (k z))
  have oI:Integrable (fun z=>old z*g z) μ:=gi.bdd_mul ui.aestronglyMeasurable (.of_forall ub)
  have mi:Integrable (fun z=>old z*(q z-read (k z))) μ:=by
    have e:Integrable (fun z=>(q z-read (k z))*old z) μ:=
      ui.bdd_mul (qm.sub ((measurable_of_countable (f:=read)).comp km)).aestronglyMeasurable (.of_forall mesh)
    simpa only [mul_comm] using e
  have zi:=unseen_old_finite_test μ k km H hi read
  change Integrable (fun z=>old z*read (k z)) μ ∧ (∫z,old z*read (k z) ∂μ)=0 at zi
  have bill:=norm_integral_le_of_norm_le (μ:=μ) (integrable_const (2*K*h))
    (.of_forall (fun z=>show ‖old z*(q z-read (k z))‖≤2*K*h from by
      rw [norm_mul];exact mul_le_mul (ub z) (mesh z) (norm_nonneg _) (by positivity)))
  have money:(∫_z:Ω,2*K*h ∂μ)=(2*K*h)*μ.real univ:=by rw [integral_const];change μ.real univ*(2*K*h)=_;ring
  rw [money] at bill
  have exactRows:(fun z=>H z*(g z-q z))=fun z=>(old z*g z+c z*(g z-q z))-
        old z*(q z-read (k z))-old z*read (k z):=by
    funext z
    change H z*_=((H z-c z)*g z+c z*(g z-q z))-(H z-c z)*(q z-read (k z))-(H z-c z)*read (k z)
    ring
  have sumI:Integrable (fun z=>old z*g z+c z*(g z-q z)) μ:=oI.add rI
  refine ⟨oI,?_⟩
  have tailIntegral:=integral_sub (sumI.sub mi) zi.1
  have innerIntegral:=integral_sub sumI mi
  have firstIntegral:=integral_add oI rI
  simp only [Pi.sub_apply] at tailIntegral innerIntegral firstIntegral
  rw [exactRows,tailIntegral,innerIntegral,firstIntegral,zi.2,sub_zero]
  have E:(∫z,old z*g z ∂μ)+(∫z,c z*(g z-q z) ∂μ)-(∫z,old z*(q z-read (k z)) ∂μ)-
      (∫z,old z*g z ∂μ)=(∫z,c z*(g z-q z) ∂μ)-(∫z,old z*(q z-read (k z)) ∂μ):=by abel
  rw [E]
  exact (norm_sub_le ..).trans (add_le_add (localPrice _ cb) bill)

end YM.Integration.FVA1Physical.Exchange.RoseCut
