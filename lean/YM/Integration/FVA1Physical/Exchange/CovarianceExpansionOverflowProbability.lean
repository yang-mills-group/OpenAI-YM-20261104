import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRegionalBadFields
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTestedCrossing

/-! A *positive probability*, on the original finite law, is paid using
only local signed pressure. Both singular local vacua and large positive
or negative complex singleton ratios are included in the one event.
The mark has its actual restoration weight w(a) throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem original_bad_sector (μ:Measure (Config G n))[IsFiniteMeasure μ](live:∀U,0<P.eval U)
    (L Y:Support n)(room:L⊆Y)(a:V)(inside:o a∈L)(t:T)(M:ℝ)(hp:0<M)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)(ε₀ ε₁:ℝ)
    (sing:∀s:Config G n→ℝ,Measurable s→UsesFinal P.p.threshold Y s→(∀g U,s (gauge g U)=s U)→
      (∀U,‖s U‖≤1)→Integrable (fun U=>s U*quietFraction A t L U) μ ∧ |∫U,s U*quietFraction A t L U ∂μ|≤ε₀)
    (mark:∀p:Config G n→ℂ,Measurable p→UsesFinal P.p.threshold Y p→(∀g U,p (gauge g U)=p U)→
      (∀U,‖p U‖≤1)→Integrable (fun U=>p U*markerFraction A L a t (w a) U) μ ∧
        ‖∫U,p U*markerFraction A L a t (w a) U ∂μ‖≤ε₁)
    (square:MemLp (fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U) 2 μ):
    M^2*μ.real (badRegion A L a t (w a) M)≤
      2*M^2*ε₀+2*M*ε₁+∫U,‖(w a:ℂ)*originalRaw A t (C.fire a) U‖^2 ∂μ:=by
  let B:=badRegion A L a t (w a) M
  let s:=B.indicator (fun _=>(1:ℝ))
  let g:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
  let p:=inverseProbe A L a t (w a) M
  let d:=fun U=>p U*markerFraction A L a t (w a) U
  let q:=fun U=>s U*quietFraction A t L U
  let u:=fun U=>p U*g U
  obtain ⟨bm,sm,ls,gs,one,pm,lp,gp,bound⟩:=bad_region_tests A L Y room a t (w a) M hp
  obtain ⟨qi,small⟩:=sing s sm ls gs one
  obtain ⟨di,rent⟩:=mark p pm lp gp bound
  change Integrable q μ at qi
  change Integrable d μ at di
  have ui:Integrable u μ:=(square.integrable (by norm_num)).bdd_mul pm.aestronglyMeasurable (.of_forall bound)
  have price:=crowd_spectator μ B bm g square
  have uf:=norm_integral_le_of_norm_le price.1 (.of_forall fun U=>show ‖u U‖≤B.indicator (fun X=>‖g X‖) U from by
    by_cases h:U∈B
    · rw [Set.indicator_of_mem h,show ‖u U‖=‖p U‖*‖g U‖ from norm_mul ..]
      exact mul_le_of_le_one_left (norm_nonneg _) (bound U)
    have no:p U=0:=Set.indicator_of_notMem h _
    simp only [u,no,zero_mul,norm_zero,Set.indicator_of_notMem h,le_refl])
  have exactMeasure:(∫U,s U ∂μ)=μ.real B:=by
    rw [show s=B.indicator (fun _:Config G n=>(1:ℝ)) from rfl,integral_indicator bm,setIntegral_const]
    simp [B]
  have account:(fun U=>M*s U)=fun U=>(u U).re-(d U).re+M*q U:=
    funext fun U=>bad_field_account A L a inside t M hp wp paid en U (live U)
  have eq:=congrArg (fun F:Config G n→ℝ=>∫U,F U ∂μ) account
  change (∫U,M*s U ∂μ)=∫U,(u U).re-(d U).re+M*q U ∂μ at eq
  have ru:Integrable (fun x=>(u x).re) μ:=ui.re
  have rd:Integrable (fun x=>(d x).re) μ:=di.re
  have im:Integrable (fun x=>(u x).re-(d x).re) μ:=ru.sub rd
  have actual:(∫x,(u x).re ∂μ)=(∫x,u x ∂μ).re:=integral_re ui
  have rer:(∫x,(d x).re ∂μ)=(∫x,d x ∂μ).re:=integral_re di
  rw [integral_const_mul,exactMeasure,integral_add im (qi.const_mul M),
    integral_sub ru rd,actual,rer,integral_const_mul] at eq
  have us:=(Complex.re_le_norm (∫U,u U ∂μ)).trans (uf.trans price.2)
  have ds:=((abs_le.mp (Complex.abs_re_le_norm (∫U,d U ∂μ))).1)
  have qs:=(le_abs_self (∫U,q U ∂μ)).trans small
  have oneCost:M*μ.real B≤Real.sqrt (∫U,‖g U‖^2 ∂μ)*Real.sqrt (μ.real B)+ε₁+M*ε₀:=by
    have rp:‖∫U,d U ∂μ‖≤ε₁:=rent
    linarith only [eq,us,ds,rp,mul_le_mul_of_nonneg_left qs hp.le]
  have gc:0≤∫U,‖g U‖^2 ∂μ:=integral_nonneg fun _=>sq_nonneg _
  have young:=sq_nonneg (M*Real.sqrt (μ.real B)-Real.sqrt (∫U,‖g U‖^2 ∂μ))
  have twice:=mul_le_mul_of_nonneg_left oneCost (show 0≤2*M by positivity)
  change M^2*μ.real B≤2*M^2*ε₀+2*M*ε₁+∫U,‖g U‖^2 ∂μ
  have paidMass:=congrArg (fun t:ℝ=>M^2*t) (Real.sq_sqrt (measureReal_nonneg:0≤μ.real B))
  nlinarith only [twice,young,Real.sq_sqrt gc,paidMass]

end YM.Integration.FVA1Physical.Exchange.RoseCut
