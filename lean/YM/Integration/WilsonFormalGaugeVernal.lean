import YM.Integration.WilsonFormalGaugeAnalytic

/-! The formal nonlinear Ward implies the real Ward used to reconstruct
the enrolled primary as curvature words. A torus is fixed in its native
rooted gauge, leaving only a pointwise global color rotation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFormalGaugeVernal
open Function Filter Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets FormalBulk08.Reef
open FormalBulk08.Broc Stationary PowerSeries PositionX.Jet PertExtension.Series
open Tested AllOrder AllOrder.Haiku AllOrder.Response AllOrder.Laplace.SigmaP
open WilsonFormalGaugeCurve WilsonFormalGaugeAnalytic
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}

private def fixed (v:ℝ→Link G n):ℝ→Link G n:=shift (scrub G n ∘ echo v)
private theorem raw (v:ℝ→Link G n)(t:ℝ):
    echo (fixed v) t=scrub G n (echo v t):=(shift_start (U:=scrub G n ∘ echo v)
      (by simp [echo,scrub_zero]) t).symm
private theorem echo_smooth (v:ℝ→Link G n)(h:ContDiffAt ℝ ω v 0):
    ContDiffAt ℝ ω (echo v) 0:=contDiffAt_id.smul h
private theorem echo_near (v:ℝ→Link G n)(h:ContDiffAt ℝ ω v 0):
    Tendsto (echo v) (𝓝 0) (𝓝 0):=by simpa [echo] using (echo_smooth v h).continuousAt.tendsto
private theorem fixed_smooth (v:ℝ→Link G n)(h:ContDiffAt ℝ ω v 0):
    ContDiffAt ℝ ω (fixed v) 0:=by
  apply shifty
  exact ((show ContDiffAt ℝ ω (scrub G n) (echo v 0) by simpa [echo] using scrub_smooth G n)).comp 0 (echo_smooth v h)

private theorem paint (W:Pap (wire G n))(law:Reef.Rite W W 1 0)(v:ℝ→Link G n)
    (h:ContDiffAt ℝ ω v 0)(k:ℕ):
    weigh v (evaluation W) k=weigh (fixed v) (evaluation W) k:=by
  let u(t:ℝ):=wisp (life v t)
  have hv:Army u 0:=by
    have enter:Army (fun x=>wisp (input G n x)) (echo v 0):=by simpa [echo] using trail_airy G n
    exact Army.comp (w:=echo v) enter (echo_smooth v h)
  apply leaf W law v (fixed v) u h (fixed_smooth v h) hv ⟨1,by funext x;simp [u,life,echo]⟩ _ k
  filter_upwards [(echo_near v h).eventually (scrub_brush G n)] with t ht
  change input G n (echo (fixed v) t)=wipeD (input G n (echo v t))
  rw [raw];exact ht

private theorem same_jet (f g:ℝ→ℝ) (hf:ContDiffAt ℝ ω f 0) (hg:ContDiffAt ℝ ω g 0)
    (he:f=ᶠ[Tested.germ]g):someJ f=someJ g:=by
  apply Aspiration.unique _ (needed hg)
  intro i
  obtain ⟨C,hC,price⟩:=needed hf i
  exact ⟨C,hC,(he.and price).mono fun t ht=>by simpa only [Pi.sub_apply,←ht.1] using ht.2⟩

/-- Every real analytic field curve has the native nonlinear Ward against
any convergent local gauge, on this same finite torus. -/
theorem original (W:Pap (wire G n))(law:Reef.Rite W W 1 0)(k:ℕ):
    Haiku.Vernal G n (evaluation W) k:=by
  constructor
  intro v w u _ hv hw _ held
  rw [paint W law v hv,paint W law w hw]
  have heal:∀ᶠ t in 𝓝 (0:ℝ),scrub G n (echo w t)=stain (u t 0) (scrub G n (echo v t)):=by
    filter_upwards [held,(echo_near v hv).eventually (scrub_linger G n)] with t ht color_ok
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

end YM.Integration.WilsonFormalGaugeVernal
end
