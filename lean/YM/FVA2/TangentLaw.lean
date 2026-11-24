import YM.FVA2.OrbitGauge
/-!
# Differentiate the finite quotient slice identity

Real gauges in the permitted chart. Identify separately the whole rooted parameter group
with its own Lie tangent space, *not* the parameter action of a constrained group with
all constants removed by the constraint on the log around nonzero fields. A later
lemma must check that the mean-zero version of the site action can indeed be used on
its particular section.
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

def actionPar (g : V→G.El) : Root D G →ₗ[ℝ] Root D G:= LinearMap.pi fun i=> (G.adjoint (g i.val)).comp (LinearMap.proj i)
omit [Fintype E] in
lemma det_par (g : V→G.El) : |LinearMap.det (actionPar (D:=D) g)|=1 := by
   unfold actionPar; rw [ LinearMap.det_pi (f:=fun i:Nonroot D=> G.adjoint (g i.val)), Finset.abs_prod];
   simp_rw [show ∀ i:Nonroot D,|LinearMap.det (G.adjoint (g i.val))|=1 from fun i=> MSBar.Pact.iso_abs _,Finset.prod_const_one]
omit [Fintype E] [Fintype V] in
lemma guarded_par (g : V→G.El) (p : Root D G) (x:V) : guarded G D (actionPar g p) x=G.adjoint (g x) (guarded G D p x) := by by_cases h:x=D.origin; subst x; rw [guard_zero,guard_zero,map_zero]; simp [guarded,actionPar,h]

private def φ (t:ℝ)(p:Root D G) : V → G.El := (expLinks G _ (t • guarded G D p))⁻¹
private def flow (A : Links E G)(p:Root D G)(t:ℝ) := θFull (D:=D) (φ t p) A
omit [Fintype E] [Fintype V] in
lemma θ_one (G : Gauge) (D : Loom V E) (A : Links E G) : θFull (D:=D) 1 A=down (expLinks G _ A) := by unfold θFull; rw [Loom.spin_one]
omit [Fintype E] [Fintype V] in
private lemma φ_zero (p:Root D G): φ 0 p=1:=by rw [φ,zero_smul,identity_zero,inv_one]
omit [Fintype E] [Fintype V] in
private lemma φ_root (p:Root D G)(t:ℝ):φ t p D.origin=1 := by simp [φ,expLinks]
omit [Fintype E] [Fintype V] in
private lemma step_form (p:Root D G) (A : Links E G) (t:ℝ) (i : E) : D.spin (φ t p) (expLinks G _ A) i=
     Maurer.step (guarded G D p (D.fromEdge i),guarded G D p (D.toEdge i)) (A i) t:= by
   simp only [φ,Loom.spin,expLinks, Pi.inv_apply, Pi.smul_apply, Maurer.step,inv_inv, Next.SectorChange.exp_negative]
section
variable (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s)
include H
omit [Fintype E] [Fintype V] in
private lemma flow_zero {A : Links E G}(p : Root D G) (hs:∀ i,A i∈s): flow A p 0=A := by rw [flow,φ_zero,θ_one]; exact funext (fun i=> H.2.2.1 (hs i))
omit [Fintype V] [Fintype E] in
private lemma flow_tan {A : Links E G} (p : Root D G) (hs:∀ i,A i∈s): HasDerivAt (flow A p) (directed G D A p) 0:= by
   refine hasDerivAt_pi.mpr fun i=>?_
   change HasDerivAt (fun t:ℝ=> G.plog (G.mat (D.spin (φ t p) (expLinks G _ A) i))) _ (0:ℝ)
   simp_rw [step_form]; exact amp _ H (hs _)
omit [Fintype V] in
private lemma flow_exp {A : Links E G} (p : Root D G) (hs:∀ i,A i∈s) :
     ∀ᶠ t:ℝ in 𝓝 0,expLinks G E (flow A p t) = D.spin (φ t p) (expLinks G _ A) := by
   have he i:∀ᶠ t:ℝ in 𝓝 0,D.spin (φ t p) (expLinks G _ A) i ∈ P:= by simp_rw [step_form]; exact walk_on _ H (hs _)
   filter_upwards [Filter.eventually_all.mpr he] with t h; exact funext fun i=> H.2.2.2.1 (h i)
omit H [Fintype V] [Fintype E] in
private lemma conjugation (p : Root D G)(g : V→G.El)(t:ℝ) : g*φ t p = φ t (actionPar g p)*g:= by
    funext x; simp only [Pi.mul_apply,φ,expLinks,Pi.smul_apply,Pi.inv_apply,guarded_par,← map_smul (G.adjoint _), runby]; group

omit [Fintype V] in
theorem action_tangent (A : Links E G)(p:Root D G) (hs:∀ i,A i∈s) (g : V→G.El) (hP:∀ i,D.spin g (expLinks G _ A) i∈ P) :
   fderiv ℝ (θFull (D:=D) g) A (directed G D A p)=directed G D (θFull (D:=D) g A) (actionPar g p):= by
   let F:= θFull (D:=D) g; have hf : DifferentiableAt ℝ F A := (differential g A (D:=D) (fun i=> θ_hot P s H _ _ (hP i))).differentiableAt
   have he : F ∘ flow A p=ᶠ[𝓝 0] flow (F A) (actionPar g p):= by
       filter_upwards [flow_exp P s H p hs] with t h; change down (D.spin g (expLinks G E (flow A p t)))= down (D.spin _ (expLinks G E (F A)))
       rw [h,right_spin g A P s H hP,D.spin_chain,D.spin_chain, conjugation]
   have hF : ∀ i,F A i∈s:= fun i=> H.2.2.2.2.1 (hP i)
   have ht:=hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (flow_tan P s H p hs) (flow_zero P s H p hs).symm
   exact ht.unique ((flow_tan P s H _ hF).congr_of_eventuallyEq he)

omit [Fintype V] in
theorem derivative_turn (A : Links E G)(T:D.Truss)(p:Root D G)(hs:∀ i,A i∈s)(ht:ContDiffAt ℝ ω (treeLog G T) A) :
    fderiv ℝ (treeLog G T) A (directed G D A p)=0:= by
   have h : (treeLog G T) ∘ flow A p=ᶠ[𝓝 0] fun _=>treeLog G T A:= by
      filter_upwards [flow_exp P s H p hs] with t h
      unfold treeLog; dsimp only [Function.comp_apply]; rw [h]
      exact congr_arg down (funext (fun i=> congr_fun (T.identify _ (φ t p) (φ_root p t)) i.val) : T.bulk (D.spin _ _) = T.bulk (expLinks G _ A))
   have hp:= (ht.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 (flow_tan P s H p hs) (flow_zero P s H p hs).symm
   exact hp.unique ((hasDerivAt_const 0 (treeLog G T A)).congr_of_eventuallyEq h)
end

lemma log_axes (G:Gauge) (T:D.Truss) : ∀ᶠ b:Free T G in 𝓝 0, ∀ p c, fderiv ℝ (treeLog G T) (enter G T b) (axes G T b (p,c))=c := by
    obtain ⟨r,hr,h⟩:=LocalH.geom_patch G; let C:=enter G T
    let F: Links E G→Free T G:= treeLog G T; have he : Tendsto C (𝓝 0) (𝓝 0):= by simpa using C.continuous_of_finiteDimensional.tendsto 0 -- theorem?
    have hdiff:=he.eventually ((priceHot G T).eventually (by simp)); let Y (b : Free T G) := F (C b); have hY: Y=ᶠ[𝓝 0] id:= board_near G T
    filter_upwards [hdiff,hY.fderiv (𝕜:=ℝ), he.eventually (Filter.eventually_all.mpr (fun i:E => ((continuous_apply i).tendsto (0:Links E G)).eventually (Metric.ball_mem_nhds (0:G.Color) hr)))] with b hb ht hx p c
    have hk : (fderiv ℝ F (C b)) ∘L C.toContinuousLinearMap=ContinuousLinearMap.id ℝ _:=by
        change fderiv ℝ (F ∘ C.toContinuousLinearMap) b=fderiv ℝ id b at ht
        rw [fderiv_id, fderiv_comp (f:=C.toContinuousLinearMap) b (show DifferentiableAt ℝ F (C b) from hb.differentiableAt (by simp)) C.toContinuousLinearMap.differentiableAt,C.toContinuousLinearMap.fderiv] at ht
        exact ht
    rw [charges,map_add, derivative_turn (H:=h r (le_refl r)) _ _ _ _ _ hx hb, zero_add]
    exact DFunLike.congr_fun hk c

lemma log_zero (G:Gauge) (T:D.Truss) : (fderiv ℝ (treeLog G T) (0:Links E G)).toLinearMap=whereL G T:= by
   apply LinearMap.ext; intro u; obtain ⟨⟨a,b⟩,rfl⟩:=(axes G T 0).surjective u
   have h := (mem_of_mem_nhds (log_axes G T)) a b; rw [map_zero] at h
   apply Eq.trans h; change b = ((axes G T 0).symm (axes G T 0 (a,b))).2; rw [LinearEquiv.symm_apply_apply]
end YM.FVA2.TreeBasis
