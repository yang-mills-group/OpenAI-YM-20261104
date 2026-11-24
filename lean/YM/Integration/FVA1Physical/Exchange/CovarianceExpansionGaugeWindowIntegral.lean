import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGradedAperture
import YM.Next.MULTISOURCE.GradeHelp
import YM.Wilson.Symmetry

/-! Factor the true physical site-gauge direction before taking a norm.
One can restrict an unpinned open link to a positive Haar patch even when
most original configurations lie outside it. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function MeasureTheory Filter Set Lattice RG Wilson
open scoped Classical BigOperators
variable {G:Gauge}{f:Side}

def endpointGauge (x:Site f)(g:G.El): Site f→G.El:=fun y=>if y=x then g else 1

def openPatch (e:Lattice.Edge (Site f))(A:Set G.El):Set (Config G f):=(fun U=>U e) ⁻¹' A

theorem open_patch_factor (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (Y:Config G f→ℂ)(E:Envelope Y)(sym:∀g U,Y (gauge (endpointGauge e.1 g) U)=Y U)
    (φ:G.El→ℂ)(pay:Envelope φ):
    (∫U,Y U*φ (U e) ∂prior G f)=(∫U,Y U ∂prior G f)*(∫t,φ t ∂G.probHaar):=by
  let μ:=prior G f;let ν:=G.probHaar
  let F:=fun U:Config G f=>Y U*φ (U e)
  let q:=fun (a:G.El) (U:Config G f)=>Y U*φ (a*U e)
  have base:Envelope F:=Multi.Leaf.multiply E (pay.comp_env (measurable_pi_apply e))
  have joint:Envelope (uncurry q):=Multi.Leaf.multiply (E.comp_env measurable_snd)
    (pay.comp_env (measurable_fst.mul ((measurable_pi_apply e).comp measurable_snd)))
  have same (a:G.El):(∫U,q a U ∂μ)=∫U,F U ∂μ:=by
    let k:=endpointGauge e.1 a
    have hp:MeasurePreserving (gauge k) μ μ:=prior_gauge k
    have change:=integral_map (φ:=gauge k) (μ:=μ) (f:=F) hp.aemeasurable base.meas.aestronglyMeasurable
    rw [hp.map_eq] at change
    rw [change]
    apply integral_congr_ae;filter_upwards with U
    show Y U*φ (a*U e)=Y (gauge k U)*φ ((gauge k U) e)
    rw [sym a U]
    simp [Lattice.gauge,k,endpointGauge,distinct]
  have inner (U:Config G f):(∫a,q a U ∂ν)=Y U*(∫a,φ a ∂ν):=by
    dsimp only [q];rw [integral_const_mul,integral_mul_right_eq_self]
  have left:(∫U,F U ∂μ)=∫a,∫U,q a U ∂μ ∂ν:=by simp_rw [same];simp only [integral_const,ν,probReal_univ,one_smul]
  calc
    _=∫a,∫U,q a U ∂μ ∂ν:=left
    _=∫U,∫a,q a U ∂ν ∂μ:=integral_integral_swap (joint.integrableC (ν.prod μ))
    _=_:=by simp_rw [inner];rw [integral_mul_const]

theorem true_patch_integral (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (A:Set G.El)(ma:MeasurableSet A)(Y:Config G f→ℂ)(E:Envelope Y)
    (sym:∀g U,Y (gauge (endpointGauge e.1 g) U)=Y U):
    (∫U in openPatch e A,Y U ∂prior G f)= (G.probHaar.real A) • (∫U,Y U ∂prior G f):=by
  let φ:=A.indicator (fun _:G.El=>(1:ℂ))
  have B:Envelope φ:=⟨measurable_const.indicator ma,1,fun x=>by by_cases hx:x∈A <;> simp [φ,hx]⟩
  have left:(fun U:Config G f=>Y U*φ (U e))=(openPatch e A).indicator Y:=by
    funext U;by_cases h:U e∈A
    · simp [φ,openPatch,h]
    · simp [φ,openPatch,h]
  have mass:(∫x,φ x ∂G.probHaar)=(G.probHaar.real A:ℂ):=by
    dsimp only [φ];rw [integral_indicator ma,integral_const];simp
  have joined:=open_patch_factor e distinct Y E sym φ B
  have meas:MeasurableSet (openPatch (G:=G) e A):=(measurable_pi_apply e) ma
  rw [left,integral_indicator meas,mass] at joined
  rw [Complex.real_smul,mul_comm]
  exact joined

/-- For the true N-inherited, unnormalized measurement at *any* live date,
a gauge transformation at any fine vertex outside the coarse roots leaves
the entire fixed-coarse-field density unchanged. -/
theorem original_open_weight (H:History G)(sel:H.Selected){N n j:ℕ}(step:j<N)
    (V:Config G (H.S.side j n))(x:Site (H.S.side (j+1) n))
    (free:∀c,(H.levels.clock.op j n).ratio.embed c≠x):
    let P:=H.rep N n (j+1);let S:=H.levels.clock.op j n
    let u:=fun U:Config G (H.S.side (j+1) n)=>S.density P.beta U V*P.eval U
    ∀ g U,u (gauge (endpointGauge x g) U)=u U:=by
  intro P S u g U
  let t:=endpointGauge x g
  have root(c):t (S.ratio.embed c)=1:=if_neg (free c)
  have unchanged:gauge (t ∘ S.ratio.embed) V=V:=by funext e;simp [Lattice.gauge,root]
  have law:=(H.levels.blocks j n).gauge P.beta U V t
  rw [unchanged] at law
  exact congrArg₂ (·*·) law (Multi.Step.path_gauge H sel N n (j+1) step t U)

end YM.Integration.FVA1Physical.Exchange.RoseCut
