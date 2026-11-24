import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionAnnularHearing

/-! First-moment currency on the literal original physical pair. Only the
selected crossing series' four numerical rows appear, the true weighted
one-source means remain attached, and no inverse cut mass is required.
The final source-scaled comparison preserves its fixed reference δ. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker QuadraticLocal Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

/-- Off the explicitly paid crowded event, every field admits a SELECTED
fixed-mask raw charge, which cancels all inverse powers above the original
single density in the restored observation. The named four physical rows
enter before absolute values; the full price is only an upper estimate. -/
theorem original_restored_pair (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e)(small:κ≤1)(t:T)(U:Config G n)(live:0<P.eval U)
    (a b:V)(s:C.Mode)(pair:s.val={a,b})(m D:ℕ)
    (far:m*(2*width P.p D)<separation (o a) (o b))
    (out:U∉crowd P.p.threshold (neighbors (m*(2*width P.p D)) (o a)) m)
    (δ:ℂ)(M:ℝ)(cap:‖((w a:ℂ)*(w b:ℂ))*δ‖≤M):
    ∃j:Fin m,U∈firstClear P.p.threshold (o a) j (width P.p D) ∧
    let L:=midBall (o a) j (width P.p D)
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    let ν:=P.activities.gas P.p U
    let ua:=(w a:ℂ)*((A.gas t U).part (C.fire a)/(ν:ℂ))
    let ub:=(w b:ℂ)*((A.gas t U).part (C.fire b)/(ν:ℂ))
    let τ:ℂ:=(w a:ℂ)*(w b:ℂ)
    let W:=max (max ‖E.part C.quiet‖ ‖(w a:ℂ)*E.part (C.fire a)‖)
      (max ‖(w b:ℂ)*E.part (C.fire b)‖ ‖τ*E.part s‖)
    W≤Real.exp (-(e*D))*(ballCost (m*(2*width P.p D))*κ) ∧
    ν*‖τ*δ‖≤ν*‖τ*(δ-filedRow A t s U)‖+2*W*(M+(1+‖ua‖)*(1+‖ub‖)):=by
  obtain ⟨j,selected,priced,det⟩:=filed_annular_pair A w wp e κ paid en small t U live a b s pair m D far out
  refine ⟨j,selected,?_⟩
  intro L E ν ua ub τ W
  let E₀:=E.part C.quiet
  let Ea:=(w a:ℂ)*E.part (C.fire a)
  let Eb:=(w b:ℂ)*E.part (C.fire b)
  let Eab:=τ*E.part s
  have gp:0<ν:=pos_of_mul_pos_right live (Real.exp_nonneg _)
  have w0:0≤W:=(norm_nonneg E₀).trans ((le_max_left ..).trans (le_max_left ..))
  have q0:‖E₀‖≤W:=(le_max_left ..).trans (le_max_left ..)
  have qa:‖Ea‖≤W:=(le_max_right ..).trans (le_max_left ..)
  have qb:‖Eb‖≤W:=(le_max_left ..).trans (le_max_right ..)
  have qab:‖Eab‖≤W:=(le_max_right ..).trans (le_max_right ..)
  have apart:a≠b:=by rintro rfl;simp at far
  have weight:Poly.toll w s=w a*w b:=by unfold Poly.toll;rw [pair,prod_insert (by simpa using apart),prod_singleton]
  have best:W≤Poly.price w E:=by
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · simpa only [Poly.quiet_toll,one_mul] using Poly.member wp C.quiet E
    · simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (wp a).le,Poly.solo_toll] using Poly.member wp (C.fire a) E
    · simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (wp b).le,Poly.solo_toll] using Poly.member wp (C.fire b) E
    simpa only [weight,τ,norm_mul,Complex.norm_real,Real.norm_of_nonneg (wp a).le,Real.norm_of_nonneg (wp b).le]
      using Poly.member wp s E
  have physical:((ν:ℂ)-E₀)*((ν:ℂ)*(τ*filedRow A t s U)-
      (Eab-ua*Eb-ub*Ea+ua*ub*E₀))=(Ea-ua*E₀)*(Eb-ub*E₀):=by
    dsimp only [Eab,Ea,Eb,E₀,ua,ub,τ]
    change ((ν:ℂ)-E.part C.quiet)*((ν:ℂ)*filedRow A t s U-
      (E.part s-((A.gas t U).part (C.fire a)/(ν:ℂ))*E.part (C.fire b)-
       ((A.gas t U).part (C.fire b)/(ν:ℂ))*E.part (C.fire a)+
       ((A.gas t U).part (C.fire a)/(ν:ℂ))*((A.gas t U).part (C.fire b)/(ν:ℂ))*E.part C.quiet))=_
      at det
    linear_combination ((w a:ℂ)*(w b:ℂ))*det
  refine ⟨best.trans priced,?_⟩
  simpa only [mul_sub] using restored_original_price ν W gp w0 E₀ Ea Eb Eab ua ub (τ*filedRow A t s U)
    q0 qa qb qab physical (τ*δ) M cap

end YM.Integration.FVA1Physical.Exchange.RoseCut
