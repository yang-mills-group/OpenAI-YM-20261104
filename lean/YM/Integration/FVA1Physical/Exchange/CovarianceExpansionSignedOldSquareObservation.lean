import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSignedOldObservation
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionUnboundedOldTest

/-! On the original finite path a correlated RMS spectator suffices.
The entire unobserved chronological part of its truncated reading remains
against the *true full* incoming singleton. Only its numerical tail and
the genuinely observable contribution have been charged. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem signed_old_square_observation {Z:Type*}[MeasurableSpace Z](μ:Measure Z)[IsFiniteMeasure μ]
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
    (C₀:ℝ)(cn:0≤C₀)(trueCap:∀U,‖(w a:ℂ)*originalRaw A t (C.fire a) U‖≤C₀)
    (H:Z→ℂ)(hm:Measurable H)(h2:MemLp H 2 μ)(K:ℝ)(kp:0<K):
    let ν:=μ.map π
    let bad:=badRegion A L a t (w a) M
    let g:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
    let q:=safeMean A L a t (w a) M
    let k:=fun z=>labelProbe M h (q (π z))
    let old:=unseenOld μ k (walletTest H K)
    Integrable (fun z=>old z*g (π z)) μ ∧
      ‖(∫z,H z*(g (π z)-q (π z)) ∂μ)-(∫z,old z*g (π z) ∂μ)‖ ≤
        ((C₀+M)/K)*(∫z,‖H z‖^2 ∂μ)+
        ((K*(Real.sqrt (∫U,‖g U‖^2 ∂ν)*Real.sqrt (ν.real bad))+K*ε₁+(K*M)*ε₀)+4*K*h*μ.real univ):=by
  intro ν bad g q k old
  have hi:=h2.integrable (by norm_num)
  have wi:=wallet_test_integrable μ H hm hi K
  have b:=signed_old_observation A μ π pm live L Y room a inside t M h mp hp wp paid en ε₀ ε₁ pressure mark square
    (walletTest H K) wi K kp.le (wallet_test_cap H K kp.le)
  obtain ⟨qm,_,_,qb,_,_,_⟩:=safe_mean_test A L Y room a t (w a) M mp
  have morph:MeasurePreserving π μ ν:=⟨pm,rfl⟩
  have fg:AEStronglyMeasurable (fun z=>g (π z)-q (π z)) μ:=
    (square.comp_measurePreserving morph).1.sub ((qm.comp pm).aestronglyMeasurable)
  have bound(z):‖g (π z)-q (π z)‖≤C₀+M:=(norm_sub_le ..).trans (add_le_add (trueCap _) (qb _))
  have tail:=wallet_test_tail μ H hm h2 K kp _ fg (C₀+M) (add_nonneg cn mp.le) bound
  exact ⟨b.1,(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add tail b.2)⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
