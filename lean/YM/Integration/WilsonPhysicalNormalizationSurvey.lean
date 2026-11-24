import YM.Integration.WilsonPhysicalNormalizationProduct
import YM.Integration.WilsonPhysicalPositionTargetRows

/-! Equivariance of the actual implicit position prescription on its oriented, filtered public branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalNormalizationSurvey
open Filter Function Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionTargetRows WilsonPhysicalNormalizationProduct
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge}{d:ℕ}{A:Screen G d}(D:Fray A){ι:Type*}{u:Filter ι}
variable (P:ι→Prediction G d)(s:ι→Change G d)

def turned (i:ι):Prediction G d:=recruit (stand (s i)) (P i)

theorem admitted (base:D.Via P (u:=u))
    (near:Tendsto (fun i=>guide G d (s i)) u (𝓝 0)):D.Via (turned P s) (u:=u):=by
  apply tendsto_pi_nhds.mpr
  intro w
  apply tendsto_pi_nhds.mpr
  intro b
  let ξ:=D.scope w
  let fields (j:Fin ξ.n):Sec G d:=Module.finBasis ℝ (Sec G d) (b j)
  let home:Fin ξ.n→Unit:=fun _=>()
  have slab:Tendsto (fun i=>rows (P i ξ.n ξ.t)) u (𝓝 (rows (reference G d ξ.n ξ.t))):=
    ((continuous_apply w).tendsto _).comp base
  have chart:Tendsto (fun i (_:Unit)=>guide G d (s i)) u (𝓝 0):=tendsto_pi_nhds.mpr fun _=>near
  have maps:=((smooth home fields).continuous.tendsto 0).comp chart
  have outcome:Tendsto (fun i=>meter home fields (fun _:Unit=>guide G d (s i))
      (rows (P i ξ.n ξ.t))) u (𝓝 (meter home fields 0 (rows (reference G d ξ.n ξ.t)))):=
    ((continuous_fst.clm_apply continuous_snd).tendsto _).comp (maps.prodMk_nhds slab)
  rw [zero] at outcome
  apply outcome.congr'
  exact Filter.Eventually.of_forall fun i=>counted home fields (P i ξ.n ξ.t) (fun _=>s i)

theorem slice (H:A.Prepared)(base:D.Via P (u:=u))
    (near:Tendsto (fun i=>guide G d (s i)) u (𝓝 0)):
    ∀ᶠ i in u, stand (s i)*stand (D.firstPass H (turned P s i))=stand (D.firstPass H (P i)):=by
  have other:=admitted D P s base near
  let next:=fun i=>D.firstPass H (turned P s i)
  have within:=approaches near (D.turns_approach H other)
  filter_upwards [D.passed H other,D.unmoor H base (fun i=>compose (s i) (next i)) within]
    with i fits unique
  have solves:Fray.SetEq A (compose (s i) (next i)) (P i):=by
    change A.D (recruit (stand (compose (s i) (next i))) (P i))=_
    rw [composed]
    exact fits
  exact (composed _ _).symm.trans (congrArg stand (unique.mp solves).symm)

theorem invariant (H:A.Prepared)(base:D.Via P (u:=u))
    (near:Tendsto (fun i=>guide G d (s i)) u (𝓝 0)):
    ∀ᶠ i in u, recruit (stand (D.firstPass H (turned P s i))) (turned P s i)=
      recruit (stand (D.firstPass H (P i))) (P i):=by
  filter_upwards [slice D P s H base near] with i same
  exact congrArg (fun F=>recruit F (P i)) same

theorem inverse (H:A.Prepared)(base:D.Via P (u:=u))
    (near:Tendsto (fun i=>guide G d (s i)) u (𝓝 0)):
    ∀ᶠ i in u, ∃ e:Sec G d≃ₗ[ℂ]Sec G d, e.toLinearMap=stand (s i) ∧
      stand (D.firstPass H (turned P s i))=e.symm.toLinearMap ∘ₗ stand (D.firstPass H (P i)):=by
  filter_upwards [slice D P s H base near,near.eventually (Fray.safe_pegs (G:=G) (d:=d))]
    with i same eqv
  rw [Fray.box,LinearEquiv.symm_apply_apply] at eqv
  let e:=LinearEquiv.ofBijective (stand (s i)) eqv
  refine ⟨e,rfl,?_⟩
  ext1 v
  apply e.injective
  change (stand (s i)*stand (D.firstPass H (turned P s i))) v=e (e.symm (_))
  rw [same,LinearEquiv.apply_symm_apply]

end YM.Integration.WilsonPhysicalNormalizationSurvey
