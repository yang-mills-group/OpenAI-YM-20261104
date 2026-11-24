import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTestedCrossing

/-! The only long-actor quantity submitted to the original joint law is
the four signed cutoff coordinates at a selected deterministic physical
collar divided by the true scalar once, times the actual singleton wages.
The exterior may depend on the entire path; its sign is kept in the
target observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Push.AbsoluteSums.Animals
open Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def fourRows (w:V→ℝ)(a b:V)(s:C.Mode)(E:Poly C):ℝ:=
  max (max ‖E.part C.quiet‖ ‖(w a:ℂ)*E.part (C.fire a)‖)
    (max ‖(w b:ℂ)*E.part (C.fire b)‖ ‖((w a:ℂ)*(w b:ℂ))*E.part s‖)

omit [Fintype V] in
private theorem four_nn (w:V→ℝ)(a b:V)(s:C.Mode)(E:Poly C):0≤fourRows w a b s E:=
  (norm_nonneg _).trans ((le_max_left ..).trans (le_max_left ..))

def crossingWallet (t:T)(a b:V)(s:C.Mode)(w:V→ℝ)(D m:ℕ)(U:Config G n):ℝ:=
  ∑j:Fin m,(firstClear P.p.threshold (o a) j (width P.p D)).indicator (fun Q=>
    fourRows w a b s (crossedCash P.activities P.p Q (fun i=>A.K.hard t i Q)
      (midBall (o a) j (width P.p D)))) U

def relativeInvoice (t:T)(a b:V)(s:C.Mode)(w:V→ℝ)(D m:ℕ)(M:ℝ)(U:Config G n):ℝ:=
  let ν:=P.activities.gas P.p U
  let ua:=(w a:ℂ)*((A.gas t U).part (C.fire a)/(ν:ℂ))
  let ub:=(w b:ℂ)*((A.gas t U).part (C.fire b)/(ν:ℂ))
  2*crossingWallet A t a b s w D m U*(M+(1+‖ua‖)*(1+‖ub‖))/ν

omit [Fintype V] in
private theorem wnn (t:T)(a b:V)(s:C.Mode)(w:V→ℝ)(D m:ℕ)(U:Config G n):
    0≤crossingWallet A t a b s w D m U:=by
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun _ _=>four_nn ..) _

/-- The first datewise relative invoice is a literal original object.
The outside-crowd term has no remaining inverse of a modified vacuum,
nor any field-independent inverse-gas hypothesis. -/
theorem relative_field (t:T)(a b:V)(s:C.Mode)(pair:s.val={a,b})(w:V→ℝ)(wp:∀v,0<w v)
    (e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)(en:0≤e)(small:κ≤1)(m D:ℕ)
    (far:m*(2*width P.p D)<separation (o a) (o b))
    (U:Config G n)(live:0<P.eval U)(out:U∉crowd P.p.threshold (neighbors (m*(2*width P.p D)) (o a)) m)
    (δ:ℂ)(M:ℝ)(cap:‖((w a:ℂ)*(w b:ℂ))*δ‖≤M):
    let τ:ℂ:=(w a:ℂ)*(w b:ℂ)
    ‖τ*δ‖≤‖τ*(δ-filedRow A t s U)‖+relativeInvoice A t a b s w D m M U:=by
  intro τ
  obtain ⟨j,sel,_,rest⟩:=original_restored_pair A w wp e κ paid en small t U live a b s pair m D far out δ M cap
  let L:=midBall (o a) j (width P.p D)
  let F:=fourRows w a b s (crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L)
  let ν:=P.activities.gas P.p U
  let ua:=(w a:ℂ)*((A.gas t U).part (C.fire a)/(ν:ℂ))
  let ub:=(w b:ℂ)*((A.gas t U).part (C.fire b)/(ν:ℂ))
  have q:0<ν:=pos_of_mul_pos_right live (Real.exp_nonneg _)
  have M0:0≤M:=(norm_nonneg _).trans cap
  have sub:F≤crossingWallet A t a b s w D m U:=by
    have pay:=(Finset.single_le_sum (s:=univ) (f:=fun k:Fin m=>
      (firstClear P.p.threshold (o a) k (width P.p D)).indicator (fun Q=>
        fourRows w a b s (crossedCash P.activities P.p Q (fun i=>A.K.hard t i Q)
          (midBall (o a) k (width P.p D)))) U) (fun k _=>Set.indicator_nonneg (fun _ _=>four_nn ..) _) (mem_univ j))
    rwa [Set.indicator_of_mem sel] at pay
  have mul:2*F*(M+(1+‖ua‖)*(1+‖ub‖))≤
    2*crossingWallet A t a b s w D m U*(M+(1+‖ua‖)*(1+‖ub‖)):=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sub (by norm_num)) (by positivity)
  change ν*‖τ*δ‖≤ν*‖τ*(δ-filedRow A t s U)‖+2*F*(M+(1+‖ua‖)*(1+‖ub‖)) at rest
  change _≤_+2*crossingWallet A t a b s w D m U*(M+(1+‖ua‖)*(1+‖ub‖))/ν
  apply (le_of_mul_le_mul_left (a:=ν) (b:=‖τ*δ‖) ?_ q)
  rw [mul_add, mul_comm ν (_ / ν), div_mul_cancel₀ _ q.ne']
  exact rest.trans (add_le_add_right mul _)

private theorem filed_measurable {Z:Type*}[MeasurableSpace Z](π:Z→Config G n)(pm:Measurable π)
    (live:∀z,0<P.eval (π z))(t:T)(a b:V)(s:C.Mode)(h:a≠b)(pair:s.val={a,b})
    (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)(en:0≤e):
    Measurable (fun z=>filedRow A t s (π z)):=by
  have ms:Measurable (A.gas t):=by
    apply Measurable.tsum;intro S
    exact Measurable.ite (P.activities.admissible_borel P.p S)
      (Finset.measurable_fun_prod _ fun i _=>(A.K.locality t i).borel) measurable_const
  let R:=fun z=>(A.gas t (π z))
  have raw:Measurable R:=ms.comp pm
  let ν:=fun z=>(R z).part C.quiet
  have nm:Measurable ν:=(Poly.part_cont _).measurable.comp raw
  let H:=fun z=>((ν z)⁻¹ • R z : Poly C)
  have hm:Measurable H:=nm.inv.smul raw
  have coord (b:C.Mode):Measurable fun z=>(H z).part b:=(Poly.part_cont _).measurable.comp hm
  have ordinary:∀z,ν z=(P.activities.gas P.p (π z):ℂ):=fun z=>
    Hard.packet_of_quiet A.K t (π z) (Hard.packet_summing _ paid en wp t _)
  have read:(fun z=>filedRow A t s (π z))=fun z=>(H z).part s-(H z).part (C.fire a)*(H z).part (C.fire b):=by
    funext z
    have q:ν z≠0:=(ordinary z) ▸ Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right (live z) (Real.exp_nonneg _)).ne'
    have norm:(H z).part C.quiet=1:=by
      change (ν z)⁻¹*(ν z)=1
      exact inv_mul_cancel₀ q
    rw [show filedRow A t s (π z)=(connected (H z)).part s by simp only [H,R,ordinary,filedRow]]
    exact twins a b s (H z) norm h pair
  rw [read]
  exact (coord s).sub ((coord _).mul (coord _))

end YM.Integration.FVA1Physical.Exchange.RoseCut
