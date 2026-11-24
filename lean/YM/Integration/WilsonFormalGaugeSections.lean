import YM.Integration.WilsonFormalGaugeVernal

/-! The receiver weights translated copies of one original field column by
an independently chosen compact-source array on this very test torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFormalGaugeSections
open Function Filter Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Jets FormalBulk08.Reef
open FormalBulk08.Broc Stationary PowerSeries PositionX.Jet
open AllOrder AllOrder.Haiku AllOrder.Response WilsonFormalGaugeCurve
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{n:Side}{k:ℕ}

def move (y:Site n)(A:Link G n):Link G n:=fun x=>A (y+x.1,x.2)
def panel (s:Site n→ℝ)(W:Pap (wire G n))(j:ℕ)(A:Link G n):ℝ:=
  ∑y,s y * evaluation W j (move y A)

private theorem smooth_move (v:ℝ→Link G n)(h:ContDiffAt ℝ ω v 0)(y:Site n):
    ContDiffAt ℝ ω (move y ∘ v) 0:=contDiffAt_pi.mpr fun i=>
      (contDiffAt_apply ℝ ℝ (y+i.1,i.2) _).comp (f:=v) 0 h

private theorem tested (W:Pap (wire G n))(base:Haiku.Vernal G n (evaluation W) k)
    (y:Site n)(v w:ℝ→Link G n)(u:ℝ→Site n→G.El)(x:G.El)
    (hv:ContDiffAt ℝ ω v 0)(hw:ContDiffAt ℝ ω w 0)
    (hu:Tendsto u (𝓝 0) (𝓝 (fun _=>x)))
    (held:life w=ᶠ[𝓝 0] fun t=>Lattice.gauge (u t) (life v t)):
    weigh (move y ∘ v) (evaluation W) k=weigh (move y ∘ w) (evaluation W) k:=by
  apply base.leaf (move y ∘ v) (move y ∘ w) (fun t z=>u t (y+z)) x
    (smooth_move v hv y) (smooth_move w hw y) (tendsto_pi_nhds.mpr fun z=>tendsto_pi_nhds.mp hu (y+z))
  filter_upwards [held] with t ht
  funext e
  have tested:=congrFun ht (y+e.1,e.2)
  change life w t (y+e.1,e.2)=u t (y+e.1) * life v t (y+e.1,e.2) * (u t (y+(e.1+step e.2)))⁻¹
  simpa only [Lattice.gauge,add_assoc] using tested

private theorem weighted_jet {ι:Type}[Fintype ι](a:ι→ℝ)(f:ι→ℝ→ℝ)
    (hf:∀i,ContDiffAt ℝ ω (f i) 0)(k:ℕ):
    someJ (fun t=>∑i,a i*f i t) k=∑i,a i*someJ (f i) k:=by
  rw [someJ,iteratedDeriv_fun_sum (fun i _=>(contDiffAt_const.mul (hf i)).of_le (by simp))]
  simp only [iteratedDeriv_const_mul_field,someJ,smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

private theorem booked (s:Site n→ℝ)(W:Pap (wire G n))(v:ℝ→Link G n)
    (hv:ContDiffAt ℝ ω v 0)(k:ℕ):
    weigh v (panel s W) k=∑y,s y*weigh (move y ∘ v) (evaluation W) k:=by
  unfold weigh
  calc
    _=∑j∈range (k+1),∑y,s y*someJ (evaluation W j ∘ move y ∘ v) (k-j):=by
      apply sum_congr rfl
      intro j _
      exact weighted_jet s (fun y=>evaluation W j ∘ move y ∘ v)
        (fun y=>smooth _ (smooth_move v hv y) _) (k-j)
    _=_:=by rw [Finset.sum_comm];simp only [mul_sum]

variable (k:ℕ)
theorem original (s:Site n→ℝ)(W:Pap (wire G n))(law:Rite W W 1 0):
    Haiku.Vernal G n (panel s W) k:=by
  constructor
  intro v w u x hv hw hu held
  rw [booked s W v hv,booked s W w hw]
  apply sum_congr rfl
  intro y _
  rw [tested W (WilsonFormalGaugeVernal.original W law k) y v w u x hv hw hu held]

end YM.Integration.WilsonFormalGaugeSections
end
