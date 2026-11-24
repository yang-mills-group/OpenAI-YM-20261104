import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSeparatedOldHearing
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionProbeMesh

/-! The outstanding cofactor on the original same path is now its
conditional-centered part times the literal physical singleton. One finite
numerical measurement of the bounded regional field is enough to pay the
whole complementary conditional-mean application at the explicit price.
There is no spatial nor temporal mesh refinement. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem signed_old_observation {Z:Type*}[MeasurableSpace Z](μ:Measure Z)[IsFiniteMeasure μ]
    (π:Z→Config G n)(pm:Measurable π)(live:∀U,0<P.eval U)
    (L Y:Support n)(room:L⊆Y)(a:V)(inside:o a∈L)(t:T)(M h:ℝ)(mp:0<M)(hp:0<h)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (ε₀ ε₁:ℝ)(pressure:∀(F:Config G n→ℂ)(K:ℝ),boundedLocal P.p.threshold Y F K→
      Integrable (fun U=>F U*scalarFraction A L t U) (μ.map π) ∧
        ‖∫U,F U*scalarFraction A L t U ∂(μ.map π)‖≤K*ε₀)
    (mark:∀(F:Config G n→ℂ)(K:ℝ),boundedLocal P.p.threshold Y F K→
      Integrable (fun U=>F U*markerFraction A L a t (w a) U) (μ.map π) ∧
        ‖∫U,F U*markerFraction A L a t (w a) U ∂(μ.map π)‖≤K*ε₁)
    (square:MemLp (fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U) 2 (μ.map π))
    (H:Z→ℂ)(hi:Integrable H μ)(K:ℝ)(kp:0≤K)(cap:∀z,‖H z‖≤K):
    let ν:=μ.map π
    let bad:=badRegion A L a t (w a) M
    let g:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
    let q:=safeMean A L a t (w a) M
    let k:=fun z=>labelProbe M h (q (π z))
    let old:=unseenOld μ k H
    Integrable (fun z=>old z*g (π z)) μ ∧
      ‖(∫z,H z*(g (π z)-q (π z)) ∂μ)-(∫z,old z*g (π z) ∂μ)‖ ≤
        (K*(Real.sqrt (∫U,‖g U‖^2 ∂ν)*Real.sqrt (ν.real bad))+K*ε₁+(K*M)*ε₀)+4*K*h*μ.real univ:=by
  intro ν bad g q k old
  obtain ⟨qm,qs,qg,qb,_,_,_⟩:=safe_mean_test A L Y room a t (w a) M mp
  have morph:MeasurePreserving π μ ν:=⟨pm,rfl⟩
  have gi:Integrable (fun z=>g (π z)) μ:=(square.comp_measurePreserving morph).integrable (by norm_num)
  have km:Measurable k:=(probe_label_measurable M h).comp (qm.comp pm)
  have fee(F:ProbeMesh M h→ℂ)(fb:∀i,‖F i‖≤K):
      ‖∫z,F (k z)*(g (π z)-q (π z)) ∂μ‖≤
        K*(Real.sqrt (∫U,‖g U‖^2 ∂ν)*Real.sqrt (ν.real bad))+K*ε₁+(K*M)*ε₀:=by
    let c:=fun U=>F (labelProbe M h (q U))
    have localTest:boundedLocal P.p.threshold Y c K:=
      ⟨(measurable_of_countable (f:=F)).comp ((probe_label_measurable M h).comp qm),
       fun U W l f=>congrArg (fun v=>F (labelProbe M h v)) (qs U W l f),
       fun k U=>congrArg (fun v=>F (labelProbe M h v)) (qg k U),fun U=>fb _⟩
    have bills:=tested_physical_singleton A ν live L Y room a inside t M mp wp paid en ε₀ ε₁ pressure mark c K kp localTest square
    change Integrable (fun U=>c U*(g U-q U)) ν ∧
      ‖∫U,c U*(g U-q U) ∂ν‖≤_ at bills
    have read:=integral_map pm.aemeasurable bills.1.aestronglyMeasurable
    exact (congrArg norm read).symm.le.trans bills.2
  have grid:=original_binned_old_hearing μ k km H hi K kp cap (fun z=>g (π z)) (fun z=>q (π z))
    gi (qm.comp pm) M (fun z=>qb (π z)) (readProbe M h) (2*h)
    (fun z=>probe_mesh_cost M h hp _ (qb (π z))) _ fee
  exact ⟨grid.1,grid.2.trans_eq (by ring)⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
