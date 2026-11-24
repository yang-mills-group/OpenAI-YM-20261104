import YM.FVA2.Orbit.Land
/-!
# Faddeev sector: be careful with the mean in this Landau prescription on the orbifold

Roams preserve the needed inversion; on the **transverse** links the constant gauge variations
remain there. This is not a claim about residual ghosts in the source redefinition of MS input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice.FiniteOrbit
open Function Set Filter Finset Topology Lattice MeasureTheory
open Pert Orb
open Orbit
open MS MS.Koszul MS.Native MS.Bare MS.Native.Chart
open LocalH
open scoped ContDiff Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "I" => PertExtension.Orb.OEdge n
local notation "Z" => Parameter G n
local notation "Y" => Potential G n
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "S" => SiteGhost G n
local notation "L" => Transverse G n
local notation "C" => G.Color
local notation "F" => Edge T
local notation "e" => G.lieExp
local notation "R₀" => Chart.roam (drive n)
open scoped Classical

section
variable {r:ℝ} (H:Geom G (G.lieExp '' Metric.ball 0 r) (Metric.ball 0 r))
variable {a:Transverse G n} (h:∀ i:Edge (Site n), includeA G n a i ∈ Metric.ball 0 r)
include H h
lemma roots_stage (p:Z) : R₀ (includeA G n a) p.val ∈ LinkP G n := by
 intro l
 have he : route (drive n) (Pert.Orb.image l) p.val = (route (drive n) l p.val).swap:= by
    let x:=l.1; let i:=l.2
    change (p.val (-x-step i),p.val ((-x-step i)+step i))=(p.val (x+step i),p.val x)
    rw [show -x-step i = -(x+step i) by abel,roots_even p, show -(x+step i)+step i= -x by abel,roots_even]
 change Maurer.volts _ ((includeA G n) a _) = _
 rw [he, show (includeA G n) a (Pert.Orb.image l) = - includeA G n a l from a.val.property l]; exact Maurer.comeback_field _ H (h l)

-- constant fields on the mean test. The conjugation retains exactly in the patch for all t (!).
def arc (a:L)(z:C)(t:ℝ)(i:F):= (G.adjoint ((e (t • z))⁻¹)) (includeA G n a i)
lemma ray (z:C)(t:ℝ)(i:F) : arc a z t i=G.plog (G.mat (Maurer.step (z,z) (includeA G n a i) t)):= by
 have hv : arc a z t i∈Metric.ball 0 r:= by unfold arc; rw [mem_ball_zero_iff,G.norm_adjoint]; exact mem_ball_zero_iff.mp (h i)
 have he:=H.2.2.1 hv
 rw [←he,show snap G _= _ from rfl,Maurer.step]
 simp only; rw [Next.SectorChange.exp_negative]; change G.plog _=G.plog _;rw [show e (arc a z t i)= _ from Maurer.runby ..]; simp
omit H h in
lemma ray_zero (a:L)(z:C)(t:ℝ) : divB (arc a z t) = 0:= by
 let x:=G.adjoint ((e (t • z))⁻¹)
 funext j; change ∑ i, (x _ - x _) = 0; simp_rw [←map_sub]; rw [←map_sum, show ∑ i:Axis,(includeA G n a (j,i)-includeA G n a (j-step i,i))= (0:C) from congr_fun (div_none a) j, map_zero]
lemma offRoy (z:C) : divB (R₀ (includeA G n a) (fun _=>z))=0:= by
    let U:= R₀ (includeA G n a) (fun _=>z); have he i: HasDerivAt (fun t:ℝ=> arc a z t i) (U i) 0:= by simp_rw [ray H h]; exact Maurer.amp _ H (h i)
    funext i; change divB U i = 0; have hh : HasDerivAt (fun t=>divB (arc a z t) i) (divB U i) 0:= by unfold divB; exact HasDerivAt.fun_sum (fun j _=> (he (i,j)).sub (he (i-step j,j)))
    simp_rw [ray_zero] at hh; exact hh.unique (hasDerivAt_const ..)
end
lemma unrooted (ev:Even n.val) : ∀ᶠ v:L in 𝓝 0, ∀ p q:S,pair v p q= root_test ev p (Orbit.vertical (traceLink G n v) (renorm G n q)):= by
 let L':= incCL G n
 obtain ⟨r,hr,H⟩:= geom_patch G; have hΞ : Tendsto (includeA G n) (𝓝 0) (𝓝 0):= aimed (show ContinuousAt (L':L→Chart.City G T) 0 from L'.cont.continuousAt) (includeA G n).map_zero
 filter_upwards [hΞ.eventually (eventually_all.mpr (fun i:F=> (continuous_apply i |>.tendsto (0:Chart.City G T)).eventually (Metric.ball_mem_nhds (0:C) hr)))] with v hv
 intro a b; let w:= renorm G n b; let z := gaugeAngles G n w; let u:= includeA G n v; let A:Potential G n:=⟨R₀ u z.val, roots_stage (H r (le_refl r)) hv z⟩
 have hA: fanEquiv ev A= Orbit.vertical (traceLink G n v) w:= rfl
 let f:= fun _:T => b.val 0; have he: z.val + f=b.val:= funext fun x=> by change atSite x _ + b.val 0=b.val x; rw [(renorm_eq b).1, sub_add_cancel]
 let c:= ((fanEquiv ev).symm (Orbit.vertical (traceLink G n v) w)).val; change linkPair (grad a.val) (R₀ u b.val)=linkPair _ c; rw [show c=A.val from congr_arg (fun p:Y=> p.val) ( (congr_arg (fanEquiv ev).symm hA.symm).trans ((fanEquiv ev).symm_apply_apply _)),← he,map_add]; rw [by_parts,by_parts]
 let D: (Chart.City G T) →ₗ[ℝ] (T→C):= LinearMap.pi fun t=> ∑ j:Axis,(LinearMap.proj (φ:=fun _=>G.Color) («R»:=ℝ) (t,j)-LinearMap.proj (t-step j,j)); have hm(u:Chart.City G T): D u=divB u:= funext fun i=> by simp [D,divB,LinearMap.sum_apply]
 rw [←hm, map_add,hm,hm,show divB (R₀ u f)=0 from offRoy (H r (le_refl r)) hv _ ,add_zero]
end YM.FVA2.Slice.FiniteOrbit
