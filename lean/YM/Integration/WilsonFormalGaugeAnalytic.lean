import YM.Integration.WilsonFormalGaugeCurve
import YM.FormalBulk08.Broc.Scrub

/-! Applying the same finite Ward identity to analytic local gauge paths
and to global color changes of any fixed coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFormalGaugeAnalytic
open Function Filter Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets FormalBulk08.Reef
open FormalBulk08.Broc Stationary PowerSeries
open AllOrder AllOrder.Haiku AllOrder.Response WilsonFormalGaugeCurve
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}

theorem leaf (W:Pap (wire G n)) (law:Reef.Rite W W 1 0)
    (v w:ℝ→Link G n) (u:ℝ→Site n→G.El)
    (hv:ContDiffAt ℝ ω v 0) (hw:ContDiffAt ℝ ω w 0) (hu:Army u 0)
    (regular:∃c,u 0=fun _=>c)
    (related:life w=ᶠ[𝓝 0] (fun t=>Lattice.gauge (u t) (life v t))) (k:ℕ):
    weigh v (evaluation W) k=weigh w (evaluation W) k:=by
  let cut (z:Rays Unit):ℝ:=z ()
  have access:ContDiffAt ℝ ω cut 0:=contDiffAt_apply ..
  have fixed (p:ℝ→Link G n):ray p 0=0:=by simp [ray]
  have raw:=law Unit (ray v) (ray w) (u∘cut) (fixed v) (fixed w)
    (ray_smooth v hv) (ray_smooth w hw) (fun i=>(hu i).comp (g:=fun x:ℝ=>G.mat (u x i)) (f:=cut) 0 access) regular
  have zero:cut 0=0:=rfl
  have atZero:Tendsto cut (𝓝 0) (𝓝 0):=zero ▸ access.continuousAt
  have heard:=raw (by
    filter_upwards [atZero.eventually related] with z hz
    simpa only [ray,cut,life,echo,comp_apply,pull_id] using hz)
  exact (coefficient W v hv k).symm.trans ((congrArg
    (fun b=>coeff k (glimpse oneRay b)) heard).trans (coefficient W w hw k))

/-- Constant conjugation acts pointwise on each measured field polynomial. -/
theorem color (W:Pap (wire G n)) (law:Reef.Rite W W 1 0) (U:Link G n) (c:G.El)(k:ℕ):
    evaluation W k (stain c U)=evaluation W k U:=by
  have known:=leaf W law (fun _=>U) (fun _=>stain c U) (fun _ _=>c)
    contDiffAt_const contDiffAt_const (Army.park _ _) ⟨c,rfl⟩
    (Eventually.of_forall fun t=>by
      simp only [life,comp_apply,echo,stain_cons,map_smul]) k
  rw [weigh_const,weigh_const] at known
  exact known.symm

end YM.Integration.WilsonFormalGaugeAnalytic
end
