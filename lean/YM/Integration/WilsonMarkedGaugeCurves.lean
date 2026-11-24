import YM.Integration.WilsonMarkedCoveredGauge
/-! Coupled analytic rays in the same physical gauge orbit. The actual gauge
may be chosen separately at each real parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedGaugeCurves
open Function Filter Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets FormalBulk08.Reef
open FormalBulk08.Broc Stationary PowerSeries PositionX.Jet PertExtension.Series
open Tested AllOrder AllOrder.Haiku AllOrder.Response AllOrder.Laplace.SigmaP
open WilsonFormalGaugeCurve WilsonFormalGaugeAnalytic
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}


open private fixed raw echo_near fixed_smooth paint same_jet from YM.Integration.WilsonFormalGaugeVernal
/-- Only an actual gauge in each sufficiently small fibre is needed. -/
theorem original (W:Pap (wire G n))(law:Reef.Rite W W 1 0)
    (v w:ℝ→Link G n)(hv:ContDiffAt ℝ ω v 0)(hw:ContDiffAt ℝ ω w 0)
    (held:∀ᶠ t in 𝓝 (0:ℝ),∃k:Site n→G.El,life w t=Lattice.gauge k (life v t))(k:ℕ):
    weigh v (evaluation W) k=weigh w (evaluation W) k:=by
  let u(t:ℝ):Site n→G.El:=if h:∃q,life w t=Lattice.gauge q (life v t) then h.choose else 1
  have related:=held.mono fun t ht=>show life w t=Lattice.gauge (u t) (life v t) by simpa only [u,dif_pos ht] using ht.choose_spec
  rw [paint W law v hv,paint W law w hw]
  have heal:∀ᶠ t in 𝓝 (0:ℝ),scrub G n (echo w t)=stain (u t 0) (scrub G n (echo v t)):=by
    filter_upwards [related,(echo_near v hv).eventually (scrub_linger G n)] with t ht color_ok
    change content (wipeD (life w t))=_
    rw [show life (G:=G) w t=Lattice.gauge (u t) (life v t) from ht,wipe_turn]
    exact color_ok (u t 0)
  have centered:∀ᶠ t in Tested.germ,fixed w t=stain (u t 0) (fixed v t):=by
    filter_upwards [heal.filter_mono nhdsWithin_le_nhds,eventually_pos] with t ht positive
    have eq:t • (fixed w t)=t • (stain (u t 0) (fixed v t)):=by
      rw [←map_smul]
      exact (raw w t).trans (ht.trans (congrArg (stain (u t 0)) (raw v t).symm))
    have res:=congrArg (fun z:Link G n=>t⁻¹•z) eq
    simpa only [smul_smul,inv_mul_cancel₀ positive.ne',one_smul] using res
  unfold weigh
  apply Finset.sum_congr rfl
  intro j _
  apply congrFun
  apply same_jet _ _ (smooth _ (fixed_smooth v hv) _) (smooth _ (fixed_smooth w hw) _)
  filter_upwards [centered] with t ht
  change evaluation W j (fixed v t)=evaluation W j (fixed w t)
  rw [ht,color W law]


end YM.Integration.WilsonMarkedGaugeCurves
end
