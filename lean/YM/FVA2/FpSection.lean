import YM.FVA2.TangentLaw
/-!
# Exact FP determinant on normalized linear slice chart

Near equality on real log charts implies equality on jets to every perturbative order.
Only one `SectionBasis` (oriented to tangent identity), one tree and root and normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeBasis
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Chart MS MS.Bare MS.Bare.Maurer Function Finset
open Push.Loops Inherit Filter Set Metric Precision Volumes
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {V E : Type} {G : Gauge} {D : Loom V E} {T : D.Truss}
variable [Fintype V][Fintype E]

/-- Work with **normalized link chart ratio** from real Haar. In chart independent
 tree expansions `fee` includes `U.scale`. This normalized version is what MS uses. -/
def density (D : Type) [Fintype D] (U:ChartRatio G) (A:Links D G) := ∏ i,U.J (A i)
lemma density_zero {I:Type} [Fintype I] (U:ChartRatio G)(H:LocalRatio U): density I U 0=1:= by simp_rw [density,Pi.zero_apply,H.anchored,Finset.prod_const_one]
lemma density_hot {I:Type} [Fintype I] (U:ChartRatio G)(H:LocalRatio U) : ContDiffAt ℝ ω (density I U) 0:= contDiffAt_prod (fun i _=> (H.germ _ (Metric.mem_ball_self H.patch)).comp (f:=fun A:Links I G=>A i) 0 (contDiff_apply ..|>.contDiffAt))

namespace SectionBasis
variable (Z:SectionBasis D T G)

def changeChart : Free T G → Free T G := treeLog G T ∘ Z.L
@[simp] lemma change_zero : Z.changeChart 0=0 := by unfold changeChart; rw [Function.comp_apply,map_zero,treeLog_zero]
lemma change_hot : ContDiffAt ℝ ω Z.changeChart 0 := by unfold changeChart; exact ((map_zero Z.L).symm ▸ priceHot G T : ContDiffAt ℝ ω (treeLog G T) (Z.L 0)).comp 0 Z.L.toContinuousLinearMap.contDiff.contDiffAt
lemma solve_one : fderiv ℝ Z.changeChart 0=ContinuousLinearMap.id ℝ _ := by
   apply ContinuousLinearMap.ext; intro x
   rw [show Z.changeChart=(treeLog G T ∘ Z.L.toContinuousLinearMap) from rfl, fderiv_comp 0 (f:=Z.L.toContinuousLinearMap) (by rw [map_zero]; exact (priceHot G T).differentiableAt (by simp)) Z.L.toContinuousLinearMap.differentiableAt,Z.L.toContinuousLinearMap.fderiv, map_zero,ContinuousLinearMap.comp_apply];
   change (fderiv ℝ _ _).toLinearMap _=_; rw [log_zero]; exact Z.agreement x
lemma fp_analytic : ContDiffAt ℝ ω Z.fpdet 0 := by
   apply Volumes.smooth_det (f:=Z.ghosts); intro y
   apply Z.projection.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun x=>directed G D (Z.L x) y)
   refine contDiffAt_pi.mpr fun i=>?_ ; apply ContDiffAt.comp (g:=volts ((guarded G D y) (D.fromEdge i),(guarded G D y) (D.toEdge i))) (f:=fun x=> Z.L x i)
   · rw [map_zero]; exact Maurer.home _
   exact ContDiffAt.comp (g:=fun x:Links E G=>x i) 0 (contDiffAt_apply ..) Z.L.toContinuousLinearMap.contDiff.contDiffAt

private lemma turn_det (A:Free T G) (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s) (h:∀ i,Z.L A i∈ s) (g : V→G.El)(hg:g D.origin=1)(hp:∀ i,D.spin g (expLinks G E (Z.L A)) i∈ P)
   (hx:θFull (D:=D) g (Z.L A)=enter G T (Z.changeChart A))
   (hz: ContDiffAt ℝ ω (treeLog G T) (enter G T (Z.changeChart A))) (hl: ContDiffAt ℝ ω (treeLog G T) (Z.L A))
   (hr:∀ p b, fderiv ℝ (treeLog G T) (enter G T (Z.changeChart A)) (axes G T (Z.changeChart A) (p,b))=b):
   |(fderiv ℝ Z.changeChart A).det| = |(fderiv ℝ (θFull (D:=D) g) (Z.L A)).det| * |Z.fpdet A| := by
   let x:=Z.L A; let y:= Z.changeChart A; let b:=enter G T y; let C:= fderiv ℝ (θFull (D:=D) g) x; let I:=axes G T y; let B:= I.symm.toLinearMap ∘ₗ C.toLinearMap ∘ₗ Z.full A; let K:=fderiv ℝ (treeLog G T) b; let Y:= fderiv ℝ Z.changeChart A
   have hy: Y=K ∘L C ∘L Z.L.toContinuousLinearMap := by
       have hC:DifferentiableAt ℝ (θFull (D:=D) g) x:= (differential g x (D:=D) (fun i=>θ_hot _ _ H _ _ (hp i))).differentiableAt
       have hm:= (root_flow g (Z.L A) T P s H hg hp).fderiv_eq (𝕜:=ℝ)
       rw [fderiv_comp (Z.L A) (by rw [hx]; exact hz.differentiableAt (by simp)) hC,hx] at hm
       unfold Y changeChart; rw [ fderiv_comp A (f:=Z.L) (hl.differentiableAt (by simp)) Z.L.toContinuousLinearMap.differentiableAt, show fderiv ℝ Z.L A=Z.L.toContinuousLinearMap from Z.L.toContinuousLinearMap.fderiv, ← hm ]; rfl
   have hpr (q : Links E G) : K q=(I.symm q).2 := by
       obtain ⟨⟨x,j⟩,rfl⟩:= I.surjective q; rw [LinearEquiv.symm_apply_apply]; exact hr x j
   have hm p : B (p,0)=(actionPar g p,0):= by
       have hρ : Z.full A (p,0)=directed G D (Z.L A) p:= by unfold full; simp
       change I.symm (fderiv ℝ (θFull (D:=D) g) (Z.L A) _) = _
       apply I.injective; rw [LinearEquiv.apply_symm_apply,hρ,action_tangent P s H (Z.L A) p h g hp,hx]; unfold I; rw [charges,map_zero,add_zero]
   have hv : LinearMap.det B=LinearMap.det (actionPar (D:=D) g) * (Y.det) := by
       apply upper_det B (actionPar (D:=D) g) Y.toLinearMap
       · exact fun p=> congr_arg Prod.fst (hm p)
       · exact fun p=> congr_arg Prod.snd (hm p)
       intro v; change (I.symm (C _)).2=Y v; rw [show Z.full A (0,v)=Z.L v from (by unfold full; simp),← hpr,hy]; rfl
   have he : LinearMap.det (I.symm.toLinearMap ∘ₗ Z.equiv.toLinearMap) = 1:= by
       let V:= axes G T 0
       rw [show I.symm.toLinearMap ∘ₗ Z.equiv.toLinearMap=(I.symm.toLinearMap ∘ₗ V.toLinearMap) ∘ₗ (V.symm.toLinearMap ∘ₗ Z.equiv.toLinearMap) from (by apply LinearMap.ext; intro a; simp),LinearMap.det_comp]; unfold I V; rw [tree_det,match_det,one_mul]
   have ht : LinearMap.det B=C.det*Z.fpdet A:= by
       unfold B; rw [Volumes.insertion_det I, show (I.symm.toLinearMap ∘ₗ Z.full A)= (I.symm.toLinearMap ∘ₗ Z.equiv.toLinearMap) ∘ₗ (Z.equiv.symm.toLinearMap ∘ₗ Z.full A) from (by apply LinearMap.ext; intro a; simp), LinearMap.det_comp,he,one_mul,projected_det]
   rw [ht] at hv; replace hv:= congr_arg abs hv; rw [abs_mul,abs_mul,det_par (D:=D) g,one_mul] at hv; exact hv.symm

omit [Fintype V] in
lemma tree_density (U : ChartRatio G) (hu: LocalRatio U) (u: Free T G): density E U (enter G T u)= density T.Bulk U u := by
   unfold density; simp_rw [enter_v]; rw [← Fintype.prod_subtype_mul_prod_subtype (T.Branch)]; simp_rw [Loom.Truss.stitch_tree,Loom.Truss.stitch_bulk,Pi.zero_apply,hu.anchored]; rw [prod_const_one,one_mul]
-- full identity.A no local derivatives passed by user.
theorem fp_identification (U:ChartRatio G) (H:LocalRatio U) : ∀ᶠ A:Free T G in 𝓝 0,
     density E U (Z.L A)* Z.fpdet A= density T.Bulk U (Z.changeChart A)* (fderiv ℝ Z.changeChart A).det := by
   obtain ⟨r,hr,hR⟩:=LocalH.geom_patch G; let s:Set G.Color:=ball 0 r; let P:=G.lieExp '' s
   let f: Free T G→ V → G.El:= T.frame ∘ expLinks G E ∘ Z.L
   let C:= Z.changeChart; have he:Tendsto Z.L (𝓝 0) (𝓝 0):= by simpa using (Z.L.continuous_of_finiteDimensional.tendsto 0)
   have hl: Tendsto (enter G T) (𝓝 0) (𝓝 0):= by simpa using ((enter G T).continuous_of_finiteDimensional.tendsto 0)
   have hc : Tendsto C (𝓝 0) (𝓝 0):= by simpa [C] using (change_hot Z).continuousAt.tendsto
   have hB:=hl.comp hc
   have hm : ∀ᶠ A:Links E G in 𝓝 0,∀ i,A i∈s∧ A i∈ball 0 U.radius:= Filter.eventually_all.mpr (fun i=> ((continuous_apply i).tendsto (0:Links E G)).eventually ( (show ∀ᶠ A:G.Color in 𝓝 0,A∈s from (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).and (Metric.ball_mem_nhds (0:G.Color) H.patch))) -- eventually
   let hJ:= priceHot G T|>.eventually (by simp)
   have hρ : ∀ᶠ u:Free T G in 𝓝 0,0<Z.fpdet u:= fp_analytic Z|>.continuousAt.eventually (lt_mem_nhds (by rw [ Z.price_one ];exact zero_lt_one))
   have hu : ∀ᶠ A:Free T G in 𝓝 0,0<(fderiv ℝ Z.changeChart A).det:= (ContinuousLinearMap.continuous_det.continuousAt.comp ((change_hot Z).fderiv_right (m:=ω) (by simp)).continuousAt).eventually (lt_mem_nhds (by rw [ Function.comp_apply, solve_one ]; exact (show 0<LinearMap.det (LinearMap.id (R:=ℝ) (M:=Free T G)) from (by rw [LinearMap.det_id]; norm_num))))
   filter_upwards [hc.eventually (log_axes G T),hB.eventually hm,he.eventually hm,he.eventually hJ,hB.eventually hJ,he.eventually (fixed_eventual G T), hu,hρ] with A hθ hp hx hd hg hG hy hw
   let b:=enter G T (C A); let g:=f A; let q:=θFull (D:=D) g (Z.L A); let H0:= hR r (le_refl r)
   have he(i:E):b i∈s:= (hp i).1
   have hff: D.spin g (expLinks G E (Z.L A))=expLinks G E b:= hG
   have hz: q=b:= by unfold q θFull; rw [hff]; exact funext fun i=> H0.2.2.1 (he i)
   have hhit (i:E):D.spin g (expLinks G E (Z.L A)) i∈ P:= by rw [hff]; exact H0.2.2.2.2.2.1 (he i)
   have ho:= turn_det Z A _ _ H0 (fun i=> (hx i).1) g (T.frame_root _) hhit hz hg hd hθ
   have hoU:= det_hFlow g (Z.L A) P s H0 U H (fun i=>(hx i).2) hhit (fun i=> by change q i∈ _; rw [hz]; exact (hp i).2)
   change density E U _ = density E U q* _ at hoU
   rw [abs_of_pos hy,abs_of_pos hw] at ho; rw [ hz ] at hoU; rw [hoU,ho, ← tree_density (D:=D) (T:=T) U H]; exact mul_assoc ..
end SectionBasis
end YM.FVA2.TreeBasis
