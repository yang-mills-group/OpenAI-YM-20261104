import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGoodRegion

/-! A tested, restored singleton after a nonbare physical step. Both
signed local pressure bills pay the complementary sector. On bad fields
the *actual* marked reading alone is integrated with its true exterior;
there is no absolute-inverse-vacuum assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def boundedLocal (θ:ℝ)(Y:Support n)(H:Config G n→ℂ)(B:ℝ):Prop:=
  Measurable H ∧ UsesFinal θ Y H ∧ (∀g U,H (Lattice.gauge g U)=H U) ∧ ∀U,‖H U‖≤B

theorem tested_physical_singleton (μ:Measure (Config G n))[IsFiniteMeasure μ](live:∀U,0<P.eval U)
    (L Y:Support n)(room:L⊆Y)(a:V)(inside:o a∈L)(t:T)(M:ℝ)(mp:0<M)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (ε₀ ε₁:ℝ)(pressure:∀(F:Config G n→ℂ)(K:ℝ),boundedLocal P.p.threshold Y F K→
      Integrable (fun U=>F U*scalarFraction A L t U) μ ∧ ‖∫U,F U*scalarFraction A L t U ∂μ‖≤K*ε₀)
    (mark:∀(F:Config G n→ℂ)(K:ℝ),boundedLocal P.p.threshold Y F K→
      Integrable (fun U=>F U*markerFraction A L a t (w a) U) μ ∧ ‖∫U,F U*markerFraction A L a t (w a) U ∂μ‖≤K*ε₁)
    (F:Config G n→ℂ)(K:ℝ)(kn:0≤K)(obs:boundedLocal P.p.threshold Y F K)
    (square:MemLp (fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U) 2 μ):
    let bad:=badRegion A L a t (w a) M
    let raw:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
    let q:=safeMean A L a t (w a) M
    Integrable (fun U=>F U*(raw U-q U)) μ ∧
      ‖∫U,F U*(raw U-q U) ∂μ‖≤K*(Real.sqrt (∫U,‖raw U‖^2 ∂μ)*Real.sqrt (μ.real bad))+
        K*ε₁+(K*M)*ε₀:=by
  intro bad raw q
  let good:=badᶜ.indicator F
  let f:=fun U=>F U*q U
  let m:=markerFraction A L a t (w a)
  let vac:=scalarFraction A L t
  obtain ⟨qm,qs,qg,qb,bm,bs,bg⟩:=safe_mean_test A L Y room a t (w a) M mp
  obtain ⟨fm,fs,fg,fb⟩:=obs
  have safeTest:boundedLocal P.p.threshold Y f (K*M):=⟨fm.mul qm,
    fun U V h b=>congrArg₂ (fun p q:ℂ=>p*q) (fs U V h b) (qs U V h b),
    fun g U=>congrArg₂ (fun p q:ℂ=>p*q) (fg g U) (qg g U),
    fun U=>(norm_mul ..).trans_le (mul_le_mul (fb U) (qb U) (norm_nonneg _) kn)⟩
  have clean:boundedLocal P.p.threshold Y good K:=by
    refine ⟨fm.indicator bm.compl,?_,?_,?_⟩
    · intro U V h b
      have same:U∈bad ↔ V∈bad:=Iff.of_eq (bs U V h b)
      by_cases hu:U∈bad
      · have hv:=same.mp hu;simp [good,hu,hv]
      have hv:V∉bad:=fun hit=>hu (same.mpr hit)
      simpa [good,hu,hv] using fs U V h b
    · intro g U
      by_cases hu:U∈bad
      · have hv: Lattice.gauge g U∈bad:=(bg g U).2 hu;simp [good,hu,hv]
      have hv:Lattice.gauge g U∉bad:=fun hit=>hu ((bg g U).1 hit)
      simpa [good,hu,hv] using fg g U
    intro U;by_cases h:U∈bad <;> simp [good,h,fb U,kn]
  obtain ⟨fi,fee⟩:=pressure f (K*M) safeTest
  obtain ⟨mi,money⟩:=mark good K clean
  change Integrable (fun U=>f U*vac U) μ at fi
  change Integrable (fun U=>good U*m U) μ at mi
  let rem:=fun U=>F U*bad.indicator raw U
  have ri:Integrable rem μ:=((square.integrable (by norm_num)).indicator bm).bdd_mul fm.aestronglyMeasurable (.of_forall fb)
  have ex:(fun U=>F U*(raw U-q U))=fun U=>rem U+good U*m U-f U*vac U:=by
    funext U
    rw [physical_singleton_split A L a inside t M wp paid en U (live U)]
    by_cases hit:U∈bad
    · have no:U∉badᶜ:=fun x=>x hit
      simp only [good,rem,f,show badRegion A L a t (w a) M=bad from rfl,Set.indicator_of_mem hit,Set.indicator_of_notMem no,add_zero,zero_mul,mul_sub]
      ring
    have yes:U∈badᶜ:=hit
    simp only [good,rem,f,show badRegion A L a t (w a) M=bad from rfl,Set.indicator_of_mem yes,Set.indicator_of_notMem hit,zero_add,mul_zero,mul_sub]
    ring
  rw [ex]
  refine ⟨(ri.add mi).sub fi,?_⟩
  have ei:Integrable (fun U=>rem U+good U*m U) μ:=ri.add mi
  rw [integral_sub ei fi,integral_add ri mi]
  obtain ⟨inc,tail⟩:=crowd_spectator μ bad bm raw square
  have weak:=norm_integral_le_of_norm_le (inc.const_mul K) (.of_forall fun U=>show
    ‖rem U‖≤K*bad.indicator (fun x=>‖raw x‖) U from by
      by_cases hit:U∈bad
      · simp only [rem,Set.indicator_of_mem hit,norm_mul]
        exact mul_le_mul_of_nonneg_right (fb U) (norm_nonneg _)
      simp [rem,hit])
  rw [integral_const_mul] at weak
  have r:=weak.trans (mul_le_mul_of_nonneg_left tail kn)
  exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add r money)) fee)

end YM.Integration.FVA1Physical.Exchange.RoseCut
