import YM.FVA2.Orbit.Blocks
/-!
# Analytic gauges at the orbit regulator

`Slice` concept: a section local to the vacuum with invertible tangent-plus-FP matrix, including
direct linear gauges. Haar density expressed by the fixed **root convention** and the relative
local tilted Jacobian. Lift through the same group product for all these choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology Lattice LocalH
open scoped ContDiff Topology Classical BigOperators Matrix
variable {G:Gauge} {n:Side}
variable (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "Θ" => R × E
variable {E}
def orbiting (v:E→Rep G n)(x:Root G n × E) := angle x.1 (v x.2)
-- FD required throughout later; keep type of Screen only analytic so don't accidentally require branch basis
structure Screen (G:Gauge)(n: Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] where
 σ : E→ Rep G n
 origin : σ 0=0
 germ : ContDiffAt ℝ ω σ 0
 valid : Bijective (fderiv ℝ (orbiting σ) 0)
namespace Screen
variable (s:Screen G n E)
def tilt := orbiting s.σ
omit [FiniteDimensional ℝ E] in
lemma stop : ∀ᶠ x:E in 𝓝 0,s.tilt (0,x)=s.σ x:= (aimed s.germ.continuousAt s.origin).eventually angle_id
omit [FiniteDimensional ℝ E] in
@[simp] lemma resting : s.tilt (0:Θ)=0:= by simp [tilt,orbiting,s.origin]
omit [FiniteDimensional ℝ E] in
lemma smooth : ContDiffAt ℝ ω s.tilt (0:Θ):= by
   let y:= fun p:Θ=> (p.1,s.σ p.2); have hy:y 0=0:= by unfold y; rw [Prod.snd_zero, Prod.fst_zero,s.origin]; rfl
   exact (hy.symm ▸ angle_germ: ContDiffAt ℝ ω (uncurry angle) (y 0)).comp (f:=y) 0 (contDiffAt_fst.prodMk (s.germ.comp 0 contDiffAt_snd))

def hurdle : (Root G n × E) ≃L[ℝ] Rep G n:= (LinearEquiv.ofBijective (fderiv ℝ s.tilt 0).toLinearMap s.valid).toContinuousLinearEquiv
lemma hurdle_eq : s.hurdle.toContinuousLinearMap=fderiv ℝ s.tilt 0:= rfl
/-- Exact relative tangent Jacobian in the rooted conventions. -/
def relative (p:Θ) := meter s.hurdle (fderiv ℝ s.tilt p)
/-- Pull the product Haar law with this FP Jacobian. -/
def weight (p:E) := hair (s.σ p)* s.relative (0,p)
lemma off_analytic : ContDiffAt ℝ ω s.relative (0:Θ):= meter_map _ (s.smooth.fderiv_right (by simp))
lemma analytic : ContDiffAt ℝ ω s.weight (0:E):= (hair_analytic.contDiffAt.comp 0 s.germ).mul (s.off_analytic.comp (f:=fun p=>(0,p)) 0 (contDiffAt_const.prodMk contDiffAt_id))
lemma head : s.weight 0=1 := by unfold weight relative; rw [s.origin,hair0,show ((0:R),(0:E))=(0:Θ) from rfl,← s.hurdle_eq, meter_self, one_mul]

local notation "Z" => Root G n
private def slide (z:Root G n)(p: Root G n × E) := (circle p.1 z,p.2)
omit [FiniteDimensional ℝ E] in
private lemma slides {z:R}{x:E} (h:DifferentiableAt ℝ (fun p:R=>circle p z) 0) :
    HasFDerivAt (slide (E:=E) z) ((fderiv ℝ (fun p:R=>circle p z) 0).prodMap (ContinuousLinearMap.id ℝ _)) (0,x) := by
    exact (h.hasFDerivAt.comp (f:=Prod.fst) (0,x) hasFDerivAt_fst).prodMk hasFDerivAt_snd
omit [FiniteDimensional ℝ E] in
private theorem roll : ∀ᶠ q:R×(R×E) in 𝓝 0,s.tilt (slide q.1 q.2) = angle q.1 (s.tilt q.2):= by
    let L:= 𝓝 (0:R×(R×E)); have h:= continuous_fst.tendsto (0:R×(R×E)); have k:= continuous_snd.tendsto (0:R×(R×E)); have hf:= (continuous_fst.tendsto (0:R×E)).comp k; have hs:= (continuous_snd.tendsto (0:R×E)).comp k; have hh : ∀ᶠ q in L, angle (circle q.2.1 q.1) (s.σ q.2.2)= angle q.1 (angle q.2.1 (s.σ q.2.2)) := (tup hf (tup h ((aimed s.germ.continuousAt s.origin).comp hs))).eventually group_joins
    exact hh
omit [FiniteDimensional ℝ E] in
lemma σ_tends : Tendsto s.σ (𝓝 0) (𝓝 0):= aimed s.germ.continuousAt s.origin
lemma orbit_density : ∀ᶠ q:R×E in 𝓝 0, hair (s.tilt q)*s.relative q = hair q.1 * s.weight q.2:= by
    let l:=𝓝 (0:R×E); have h:= continuous_fst.tendsto (0:R×E); have k:= continuous_snd.tendsto (0:R×E)
    have hp : Tendsto (fun _:Θ=> (0:R)) l (𝓝 0):= tendsto_const_nhds; have hK:= tup hp k
    filter_upwards [(s.smooth.eventually (by simp)),hK.eventually (s.smooth.eventually (by simp)), h.eventually (gate_right (G:=G)),(tup hp h).eventually diff_circle,k.eventually s.stop,h.eventually left_turn,(tup h (s.σ_tends.comp k)).eventually angle_wind,(tup h hK).eventually (s.roll.eventually_nhds)] with q hq hx hU hW hl hJ hψ hR
    let z:=q.1; let v:=s.σ q.2; let p: Θ:= (0,q.2); let T:=fderiv ℝ s.tilt; let S:=slide (E:=E) z; let A:=angle z; let M:=fderiv ℝ (angle z) v; let K:=fderiv ℝ (fun x:R=>circle x z) 0; let N:= K.prodMap (ContinuousLinearMap.id ℝ E)
    have hZ: DifferentiableAt ℝ s.tilt q:= hq.differentiableAt (by simp)
    have hP : DifferentiableAt ℝ s.tilt p:= hx.differentiableAt (by simp)
    have hg: hair z * K.det=1:=hU; have hj: S p=q:= Prod.ext hJ rfl; have hsp:s.tilt p=v:= hl
    have he : s.tilt ∘ S =ᶠ[𝓝 p] A ∘ s.tilt:= ((continuous_const (y:=q.1)).prodMk continuous_id |>.tendsto p).eventually hR
    have ht : T q ∘L N = M ∘L T p := by
       have hu:HasFDerivAt (s.tilt ∘ S) (T q ∘L N) p:= (hj.symm ▸ (hZ.hasFDerivAt : HasFDerivAt s.tilt (T q) q) : HasFDerivAt s.tilt (T q) (S p)).comp p (slides hW.2)
       have hA : HasFDerivAt A M (s.tilt p):= hsp.symm ▸ (hψ.2.hasFDerivAt : HasFDerivAt A M v)
       exact (hu.congr_of_eventuallyEq he.symm).unique (hA.comp p hP.hasFDerivAt)
    have he' : K.det*s.relative q = M.det*s.relative p:= by unfold relative; rw [mul_comm,←cost_left,← show N.det=K.det from (LinearMap.det_prodMap K.toLinearMap LinearMap.id).trans (by rw [LinearMap.det_id, mul_one]),←cost_right]; exact congr_arg (meter s.hurdle) ht
    have hv' : hair (s.tilt q)*M.det=hair v:= hψ.1
    change hair (s.tilt q)*s.relative q= hair z * (hair v * s.relative p); rw [←hv', mul_assoc, ←mul_assoc (hair (s.tilt q))] -- adjust
    calc
      _ = hair z * (hair (s.tilt q) * (K.det *s.relative q)):= by rw [mul_left_comm,←mul_assoc (hair z),hg,one_mul]
      _ = _:= by rw [he']; ring
end Screen
end YM.FVA2.Orbit
