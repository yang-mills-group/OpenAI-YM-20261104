import YM.FVA2.Repoint
/-!
# Full Faddeev–Popov chart in chosen based convention

Without staying on the strict slice. Produces the Jacobian for inserting a rescaled Gaussian
(instead of delta) in arbitrary linear transverse conditions almost automatically. Uses tree/root
Haar determinant proved in preceding modules. This is **only** the quotient by *based* site
gauges; it doesn't mean one can insert mean-zero/raw determinants around off-slice fields with
arbitrary smearing. A param basis change at the tree: specified by Repoint.issue incl all
possible targets K. Use all small-link derivatives of the same Jac, analytic near trivial orbit.
No claim of neighbour radius uniformity beyond what is needed on EACH finite regulator.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.TreeBasis.SectionBasis
open PertExtension PertExtension.Chart FormalOPE.RG10 FormalOPE.RG10.BlockGauge Gauge
open Function Filter Set Metric Volumes Precision Push.Loops
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {V E : Type} [Fintype V][Fintype E]
variable {D : Loom V E} {T : D.Truss} {G: Gauge}
variable (Z:SectionBasis D T G)

local notation "F" => Free T G
local notation "P" => Root D G

def Aghost (A:Links E G):= Z.projection.comp (directed G D A)
def AP (A:Links E G):=LinearMap.det (Aghost Z A)
lemma slice_det (b:F): AP Z (Z.L b)= Z.fpdet b:= rfl
lemma Agg_alive : AP Z 0=1:= by rw [← map_zero Z.L,slice_det]; exact Z.price_one
lemma Agg_hot : ContDiffAt ℝ ω (Z.AP) 0:= by
   apply Volumes.smooth_det (f:=Z.Aghost); intro y
   apply Z.projection.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun x=>directed G D x y)
   refine contDiffAt_pi.mpr fun i=>?_; exact (MS.Bare.Maurer.home ((guarded G D y) (D.fromEdge i),(guarded G D y) (D.toEdge i))).comp (f:=fun x:Links E G=>x i) 0 (contDiffAt_apply ..)

-- a normalized FP chart on the full space P × F using equiv for link basis
def anchor : P × F→ P × F:= fun x=> (x.1,treeLog G T (Z.equiv x))
@[simp] lemma anchored : anchor Z 0=0:= Prod.ext rfl (by unfold anchor; rw [map_zero,treeLog_zero]; rfl)
lemma anchor_hot : ContDiffAt ℝ ω (anchor Z) 0:= ContDiffAt.prodMk contDiffAt_fst <| ((show ContDiffAt ℝ ω (treeLog G T) (Z.equiv 0) from ((map_zero Z.equiv).symm ▸ (priceHot G T))).comp 0 Z.equiv.toContinuousLinearEquiv.contDiff.contDiffAt)
lemma anchor_one : fderiv ℝ (anchor Z) 0=ContinuousLinearMap.id ℝ _:= by
    let H:=treeLog G T; have he: ContDiffAt ℝ ω H (Z.equiv 0):=by rw [map_zero]; exact priceHot G T
    let L:= Z.equiv.toContinuousLinearEquiv.toContinuousLinearMap
    have ht: fderiv ℝ (anchor Z) 0=(ContinuousLinearMap.fst ℝ P F).prod ((fderiv ℝ H (Z.equiv 0)) ∘L L):= ( ((ContinuousLinearMap.fst ℝ P F).hasFDerivAt).prodMk (((he.differentiableAt (by simp)).hasFDerivAt).comp 0 L.hasFDerivAt) ).fderiv
    rw [ht,map_zero]; apply ContinuousLinearMap.ext; intro b; refine Prod.ext rfl ?_; change (fderiv ℝ (treeLog G T) 0).toLinearMap (Z.equiv b)=b.2; rw [log_zero, ← equiv_right, LinearEquiv.symm_apply_apply] -- rw location

private lemma jac_alg (A:Links E G)(x : P × F)(he:Z.equiv x=A) (Ω : Set G.El) (s : Set G.Color)(H:LocalH.Geom G Ω s)(h:∀ i,A i∈s)(g:V→G.El)(hg:g D.origin=1)(hp:∀ i,D.spin g (expLinks G E A) i∈Ω) (hf : Z.AP A ≠ 0)
    (hx:θFull (D:=D) g A=enter G T (treeLog G T A))
    (hz':ContDiffAt ℝ ω (treeLog G T) (enter G T (treeLog G T A)))
    (hl:ContDiffAt ℝ ω (treeLog G T) A)
    (hr:∀ p b, fderiv ℝ (treeLog G T) (enter G T (treeLog G T A)) (axes G T (treeLog G T A) (p,b))=b):
    |(fderiv ℝ (anchor Z) x).det|= |(fderiv ℝ (θFull (D:=D) g) A).det| * |Z.AP A| := by
   let y:=treeLog G T A; let b:=enter G T y; let C:= fderiv ℝ (θFull (D:=D) g) A; let I:= axes G T y
   let e:=Z.equiv; let R:= LinearMap.coprod (directed G D A) Z.L; let B:= I.symm.toLinearMap ∘ₗ C.toLinearMap ∘ₗ R; let K:=fderiv ℝ (treeLog G T) A; let Y:= fderiv ℝ (treeLog G T) b
   let X:= ( e.symm.toLinearMap ∘ₗ R); let Aρ:= fderiv ℝ (anchor Z) x
   let L:= e.toContinuousLinearEquiv.toContinuousLinearMap
   have ha: Aρ=(ContinuousLinearMap.fst ℝ P F).prod (K ∘L L):= by
        subst A; exact ((ContinuousLinearMap.fst ℝ P F).hasFDerivAt.prodMk (((hl.differentiableAt (by simp)).hasFDerivAt).comp _ L.hasFDerivAt)).fderiv
   have hy (q : Links E G) : K q=(I.symm (C q)).2:= by
        have hz(q:Links E G): Y q=(I.symm q).2:= by
            obtain ⟨⟨p,x⟩,rfl⟩:=I.surjective q; rw [LinearEquiv.symm_apply_apply]; exact hr p x
        rw [←hz]; have hC:DifferentiableAt ℝ (θFull (D:=D) g) A:= (differential g A (D:=D) (fun i=>θ_hot _ _ H _ _ (hp i))).differentiableAt
        have hm:= (root_flow g A T Ω s H hg hp).fderiv_eq (𝕜:=ℝ)
        rw [fderiv_comp A (by rw [hx]; exact ((show ContDiffAt ℝ ω (treeLog G T) b from hz').differentiableAt (by simp))) hC,hx] at hm; exact (DFunLike.congr_fun hm q).symm
   have hpR (p:P): R (p,0)=directed G D A p:= by unfold R; simp
   have hpL (f:F): R (0,f)=Z.L f:= by unfold R; simp
   have hq(p:P): B (p,0)=( actionPar g p,0):= by
        apply I.injective; change I (I.symm (C (R _)))= _; rw [LinearEquiv.apply_symm_apply,hpR]; unfold C; rw [action_tangent Ω s H A p h g hp,hx]; unfold I; rw [charges,map_zero,add_zero]
   let H₁:= K.toLinearMap ∘ₗ Z.L
   have hAX: LinearMap.det (Aρ.toLinearMap ∘ₗ X)= Z.AP A * LinearMap.det H₁ := by
         apply upper_det _ (Aghost Z A)
         · intro p; rw [ha]; change (e.symm (R _)).1=_; rw [hpR]; rfl
         · intro p; rw [ha]; change K (e (e.symm _))=_; rw [LinearEquiv.apply_symm_apply,hpR,hy,←hpR]; exact congr_arg Prod.snd (hq p)
         intro c; rw [ha]; change K (e (e.symm _))=_; rw [LinearEquiv.apply_symm_apply,hpL]; rfl
   have hX: LinearMap.det X=Z.AP A:= by
         have hXb(c:F): X (0,c)=(0,c):= by
             apply e.injective; change e (e.symm _)=_; rw [ LinearEquiv.apply_symm_apply,hpL]; unfold e; rw [Z.equiv_acts,map_zero,zero_add]
         apply (lower_det X (Aghost Z A) (LinearMap.id (M:=F) (R:=ℝ)) ?_ (fun c=>congr_arg Prod.fst (hXb c)) (fun c=>congr_arg Prod.snd (hXb c)))|>.trans (show _=Z.AP A from (by rw [LinearMap.det_id,mul_one]; rfl))
         intro p; change (e.symm (R _)).1=_; rw [hpR]; rfl
   have hB: LinearMap.det B= LinearMap.det (actionPar (D:=D) g) * LinearMap.det H₁ := by refine upper_det _ _ _ (fun p=> congr_arg Prod.fst (hq p)) (fun p=>congr_arg Prod.snd (hq p)) (fun c=>?_); change (I.symm (C (R _))).2= _; rw [hpL,←hy]; rfl
   have he : LinearMap.det (I.symm.toLinearMap ∘ₗ e.toLinearMap)=1:= by
       let J:= axes G T 0
       rw [show I.symm.toLinearMap ∘ₗ e.toLinearMap=(I.symm.toLinearMap ∘ₗ J.toLinearMap) ∘ₗ (J.symm.toLinearMap ∘ₗ e.toLinearMap) from (by apply LinearMap.ext; intro a; simp), LinearMap.det_comp]; unfold I J e; rw [tree_det,match_det,one_mul]
   have hh: LinearMap.det B= C.det * Z.AP A := by
       unfold B; rw [Volumes.insertion_det I, show (I.symm.toLinearMap ∘ₗ R)= (I.symm.toLinearMap ∘ₗ e.toLinearMap) ∘ₗ X from (by unfold X; apply LinearMap.ext; intro a; simp), LinearMap.det_comp,he,hX,one_mul]
   change |LinearMap.det Aρ.toLinearMap|=|C.det| * |_|; rw [LinearMap.det_comp,hX,mul_comm (Z.AP A)] at hAX; rw [mul_right_cancel₀ hf hAX]; rw [hh] at hB; replace hB:= congr_arg abs hB; rw [abs_mul,abs_mul,det_par, one_mul] at hB; exact hB.symm


/-- The actual link-Haar jacobian (around small log fields). -/
theorem flash (U:ChartRatio G)(H:LocalRatio U) : ∀ᶠ x:P × F in 𝓝 0, density E U (Z.equiv x) * Z.AP (Z.equiv x) = density T.Bulk U (Z.anchor x).2 * (fderiv ℝ Z.anchor x).det := by
   obtain ⟨r,hr,hR⟩:=LocalH.geom_patch G
   let s:Set G.Color:= ball 0 r; let Ω:= G.lieExp '' s
   let f:Links E G→V→G.El:= T.frame ∘ expLinks G E
   let C:=treeLog G T; have he:Tendsto Z.equiv (𝓝 0) (𝓝 0) := by convert! (Z.equiv.toContinuousLinearEquiv.continuous.tendsto 0) using 2; rw [map_zero]
   have hc:Tendsto C (𝓝 0) (𝓝 0):= by simpa [treeLog_zero] using! ((priceHot G T).continuousAt.tendsto)
   have hB : Tendsto (enter G T) (𝓝 0) (𝓝 0) := by simpa using ((enter G T).continuous_of_finiteDimensional.tendsto 0)
   have hm : ∀ᶠ A:Links E G in 𝓝 0,∀ i,A i∈ s ∧ A i∈ ball 0 U.radius:= Filter.eventually_all.mpr (fun i=> ((continuous_apply i).tendsto (0:Links E G)).eventually ((Metric.ball_mem_nhds (0:G.Color) hr : {x|x∈s}∈𝓝 0) |> (show {x|x∈s}∈𝓝 0→_ from (fun h=> Filter.inter_mem h (Metric.ball_mem_nhds (0:G.Color) H.patch))))) -- shorthand
   let hJ:= priceHot G T|>.eventually (by simp)
   have hρ : ∀ᶠ u:Links E G in 𝓝 0,0<Z.AP u := Agg_hot Z|>.continuousAt.eventually (lt_mem_nhds (by rw [ Agg_alive ];exact zero_lt_one))
   have hu : ∀ᶠ A:P × F in 𝓝 0,0<(fderiv ℝ Z.anchor A).det:= (ContinuousLinearMap.continuous_det.continuousAt.comp ((anchor_hot Z).fderiv_right (m:=ω) (by simp)).continuousAt).eventually (lt_mem_nhds (by rw [ Function.comp_apply, anchor_one ]; exact (show 0<LinearMap.det (LinearMap.id (R:=ℝ) (M:=(P × F))) from (by rw [LinearMap.det_id]; norm_num))))
   filter_upwards [he.eventually (hc.eventually (log_axes G T)), he.eventually (hc.eventually (hB.eventually hm)), he.eventually hm, he.eventually (hc.eventually (hB.eventually hJ)),he.eventually hJ, he.eventually (fixed_eventual G T), he.eventually hρ,hu] with x hx hp ha hpb hab hg hor hy
   let A:=Z.equiv x; let b:= enter G T (C A); let g:=f A; let q:=θFull (D:=D) g A; let H0:= hR r le_rfl
   have hs(i:E):b i∈s:= (hp i).1
   have he : D.spin g (expLinks G E A)= expLinks G E b:= hg; have hz:q=b:= by unfold q θFull; rw [he]; exact funext fun i=> H0.2.2.1 (hs i)
   have hhit(i:E):D.spin g (expLinks G E A) i∈Ω:= by rw [he]; exact H0.2.2.2.2.2.1 (hs i)
   have ho:= jac_alg Z A x rfl _ _ H0 (fun i=> (ha i).1) g (T.frame_root _) hhit ( show Z.AP A ≠0 from hor.ne') hz hpb hab hx
   have hoU:= det_hFlow g A Ω s H0 U H (fun i=>(ha i).2) hhit (fun i=> by change q i ∈ _; rw [hz]; exact (hp i).2)
   change density E U _ = density E U q*_ at hoU
   rw [ hz ] at hoU; change density E U A* Z.AP A=_; rw [abs_of_pos hy,abs_of_pos (show 0<Z.AP A from hor)] at ho; rw [hoU, tree_density (T:=T) U H (u:=C A),ho]; exact mul_assoc ..

end YM.FVA2.TreeBasis.SectionBasis
