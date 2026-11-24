import YM.FVA2.Orbit.Metered
import YM.MS.Wilson.Gauge
/-!
# Vertical tangent to all these strict gauges
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology Lattice PertExtension PertExtension.Orb LocalH
open MS.Native MS.Bare
open scoped ContDiff Topology MeasureTheory Matrix.Norms.Frobenius Classical BigOperators
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "I" => OEdge n
local notation "θ" => R × E
local notation "e" => G.lieExp

def Ends (i : I) : Root G n →ₗ[ℝ] Maurer.Ends G := LinearMap.prod (atSite i.val.1) (atSite (i.val.1+step i.val.2))
/-- The tangent generator at representative coordinates. -/
def vertical (p:Rep G n) : Root G n →ₗ[ℝ] Rep G n:= LinearMap.pi fun i:I=> Maurer.voltage (p i) ∘ₗ Ends i
lemma tilted : ∀ᶠ p:V in 𝓝 0,DifferentiableAt ℝ (fun z=>angle z p) (0:R):= by
 let v:=fun p:V=> ((0:R),p); have ht:Tendsto v (𝓝 0) (𝓝 0):= tup tendsto_const_nhds tendsto_id
 filter_upwards [ht.eventually (angle_germ.eventually (by simp))] with p hp
 let f:=uncurry (angle (n:=n) (G:=G)); exact (hp.differentiableAt (by simp)).comp (g:=f) (f:=fun z=>(z,p)) 0 (differentiableAt_id.prodMk (differentiableAt_const _))
private lemma played_t (i:I) (z:R) (p:V) (u:ℝ) : play (u • z) p i.val=Maurer.step (Ends i z) (p i) u:= by
    unfold play Lattice.gauge gang Maurer.step; rw [ show ignite p _=_ from lift_at _ i, map_smul,map_smul,Next.SectorChange.exp_negative,inv_inv];rfl
lemma vertical_D : ∀ᶠ p:V in 𝓝 0, fderiv ℝ (fun z:R=>angle z p) 0=(vertical p).toContinuousLinearMap:= by
 let v:=fun p:V=> ((0:R),p); have ht:Tendsto v (𝓝 0) (𝓝 0):= tup tendsto_const_nhds tendsto_id
 obtain ⟨r,hr,H⟩:=geom_patch G; let S:= Metric.ball (0:G.Color) r
 filter_upwards [eventually_all.mpr (fun i:I=> (continuous_apply i|>.tendsto (0:V)).eventually (Metric.ball_mem_nhds (0:G.Color) hr)), ht.eventually ((physical (G:=G) (n:=n)).eventually_nhds), angle_id (G:=G) (n:=n), tilted (G:=G) (n:=n)] with p hp he hw hh
 apply ContinuousLinearMap.ext; intro z; funext i
 let f:=fun z:R=>angle z p; let l := Maurer.lie G; let x:=p i; let D:=fderiv ℝ l x 
 let ζ:=fderiv ℝ f 0; let y:ℝ→R:=fun t=>t • z; have hz:HasDerivAt y z 0:= by simpa [y] using! ((hasDerivAt_id' (0:ℝ)).smul_const z)
 have hy:y 0=0:= by simp [y]
 let k: V→L[ℝ] G.Color:= ContinuousLinearMap.proj i
 let g:= k ∘ f; have hm:g 0=x:= congr_fun hw i
 have hV : HasFDerivAt (l ∘ g) (D ∘L k ∘L ζ) 0:= (hm.symm ▸ ((G.exp_jet.differentiable (by simp) x).hasFDerivAt) : HasFDerivAt l D (g 0)).comp (f:=g) 0 (k.hasFDerivAt.comp (f:=f) 0 hh.hasFDerivAt)
 let s:=Maurer.step (Ends i z) x; have he' : (fun t=>G.mat (s t)) =ᶠ[𝓝 0] ((l ∘ g) ∘ y):= by
    filter_upwards [((aimed hz.continuousAt hy).prodMk_nhds (tendsto_const_nhds (x:=p))).eventually he] with t hu
    apply congr_arg G.mat; exact ( (played_t i z p t).symm.trans (congr_fun hu i.val).symm ).trans (show ignite _ _=_ from lift_at _ i)
 have hb:= ((hV.comp_hasDerivAt_of_eq 0 hz hy.symm).congr_of_eventuallyEq he').unique (Maurer.step_tan (Ends i z) x)
 apply Maurer.identifies (H r (le_refl r)) (hp i); exact hb.trans (Maurer.voltf (Ends i z) (H r (le_refl r)) (hp i)).symm
lemma axes_later (σ:E→ V) (h:ContDiffAt ℝ ω σ 0)(ht:σ 0=0): ∀ᶠ x:E in 𝓝 0,∀ z:R, ∀ y:E,fderiv ℝ (orbiting σ) (0,x) (z,y)=vertical (σ x) z + fderiv ℝ σ x y:= by
 let Ψ:= orbiting σ; have hF : (fun x:E=>Ψ (0,x))=ᶠ[𝓝 0] σ:= (aimed h.continuousAt ht).eventually angle_id
 have h' : ContDiffAt ℝ ω Ψ 0:= by
    let f:=fun x:θ=> (x.1,σ x.2); have hz:f 0=0:= by simp [f,ht]
    exact (hz.symm ▸ angle_germ : ContDiffAt ℝ ω (uncurry angle) (f 0)).comp (f:=f) 0 (contDiffAt_fst.prodMk (h.comp 0 contDiffAt_snd))
 filter_upwards [(aimed h.continuousAt ht).eventually vertical_D,hF.fderiv (𝕜:=ℝ), ((continuous_const (y:=(0:R))).prodMk continuous_id |>.tendsto (0:E)).eventually (h'.eventually (by simp))] with x hx hy hz
 intro z y; change fderiv ℝ Ψ _ _ = _
 rw [deriv_split Ψ (show DifferentiableAt ℝ Ψ (0,x) from hz.differentiableAt (by simp)), show fderiv ℝ (fun u:R=>Ψ (u,x)) 0 = _ from hx, show fderiv ℝ (fun u:E=> Ψ (0,u)) x = _ from hy]; rfl
lemma vertical_flat (z:R) : vertical (0:V) z = -(touches G n (Pert.Orb.gZ (gaugeAngles G n z))) := by
 funext i; rw [show vertical (0:V) z i=_ from (Maurer.volt_zero (Ends i z))]; change _-_ = - ((atSite i.val.1 z)-(atSite (i.val.1+step i.val.2) z)); rw [neg_sub];rfl
end YM.FVA2.Orbit
