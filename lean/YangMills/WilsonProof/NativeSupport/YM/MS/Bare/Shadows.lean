import YM.MS.Bare.Shadows
import YM.MS.Bare.Tangent
import YM.LocalH.Haar

/-!
# Symmetries of the infinitesimal link fields

Use inversion reflecting base of oriented links. Haar is local ratio spin,
 with the sign of its log fixed. Color transformation acts simultaneously on all sites.
   We'll take all jets in physical color coords.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Maurer
open Function Set Filter Metric LocalH Next.SectorChange
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}
variable (x : Ends G)
local notation "E"=> lie G
section
variable {U:Set G.El}{r:ℝ}(H:Geom G U (ball 0 r)){a : C G}(ha:a∈ball 0 r)
lemma comeback (a:C G) : E (-a)=star (E a):= by unfold lie; rw [exp_negative,G.mat_inv]
lemma comeback_d (a v:C G) : fderiv ℝ E (-a) (-v)=star (fderiv ℝ E a v):= by
   let T : G.Mat→L[ℝ] G.Mat:= (starL ℝ).toContinuousLinearMap
   let V : C G→L[ℝ] C G:= -1
   have h : E ∘ V=T ∘ E:= funext fun a=> comeback a
   have he : Differentiable ℝ E:= G.exp_jet.differentiable (by simp)
   have hv := (fderiv_comp a (g:=E) (f:=⇑V) (he _) V.differentiableAt); rw [h,fderiv_comp a T.differentiableAt (he a),V.fderiv] at hv
  
   apply Eq.trans (DFunLike.congr_fun hv.symm v); exact DFunLike.congr_fun (show fderiv ℝ T (E a)=T from T.fderiv) (fderiv ℝ E a v)
include H ha
lemma comeback_field : volts x.swap (-a)= -volts x a:= by
   have ht : -a ∈ ball 0 r:= by simpa using ha
   apply identifies H ht; rw [voltf x.swap H ht, comeback_d, voltf x H ha]; simp [mx,comeback, G.colorMat_skew,sub_eq_add_neg,add_comm]
omit H ha in
lemma volt_back : ∀ᶠ a:C G in 𝓝 0, volts x.swap (-a)= -volts x a:= by obtain ⟨r,hr,h⟩:=geom_patch G; exact Eventually.mono (ball_mem_nhds _ hr) (fun a ha=> comeback_field x (h r (le_refl r)) ha)

variable (u:G.El)
omit H ha
-- conjugation linear
lemma runby (u:G.El)(a:C G): G.lieExp (G.adjoint u a)=u*G.lieExp a*u⁻¹ := by
    apply G.mat_injective; simp only [G.mat_mul,G.mat_inv,G.mat_lieExp,G.mat_adjoint]; exact G.exp_conjugate ..
lemma runservo (a:C G): E (G.adjoint u a)=runmat u (E a):= by unfold lie; rw [runby,G.mat_mul,G.mat_mul]; rfl
lemma runhere (a v:C G) : fderiv ℝ E (G.adjoint u a) (G.adjoint u v)=runmat u (fderiv ℝ E a v):= by
   let V := (G.adjoint u).toContinuousLinearMap; have h : E ∘ V=runmat u ∘ E:= funext fun a=>runservo u a
   have he : Differentiable ℝ E:= G.exp_jet.differentiable (by simp); have hv := fderiv_comp a (g:=E) (f:=⇑V) (he _) V.differentiableAt
   rw [h,fderiv_comp a (runmat u).differentiableAt (he a),V.fderiv] at hv
   apply Eq.trans (DFunLike.congr_fun hv.symm v); exact DFunLike.congr_fun (show fderiv ℝ (runmat u) (E a)=(runmat u) from (runmat u).fderiv) (fderiv ℝ E a v)
include H ha
lemma runvolt : volts (Prod.map (G.adjoint u) (G.adjoint u) x) (G.adjoint u a)=G.adjoint u (volts x a):= by
   have he:G.adjoint u a∈ball 0 r:= by simpa using ha
   apply identifies H he; rw [voltf _ H he,runhere,voltf x H ha, runservo]; simp only [mx,LinearMap.coe_mk, AddHom.coe_mk,Prod.map_fst,Prod.map_snd,map_sub,G.mat_adjoint,runprod]; rfl
end

-- true normalized Haar germs: use any certified LocalRatio, trace determinant on translated test subspace.
open Precision
def lac (a:C G) := Real.log (spin G a)
lemma lives (G:Gauge): ∀ᶠ a:C G in 𝓝 0,0 < spin G a:= (spin_deriv G 0).continuousAt.eventually (lt_mem_nhds (by rw [spin_zero]; exact zero_lt_one))
lemma hlog (G:Gauge): ContDiffAt ℝ ω (lac (G:=G)) 0:= by
   unfold lac; exact ((Real.contDiffAt_log).mpr (show spin G 0≠0 from (spin_zero G).symm ▸ one_ne_zero)).comp (f:=spin G) 0 (spin_deriv G 0) -- order
lemma real_ratio {Z:ChartRatio G}(h:LocalRatio Z): Z.J=ᶠ[𝓝 0] spin G:= by
   filter_upwards [lives G,isOpen_ball.mem_nhds (mem_ball_self (x:=0) h.patch)] with x hx hv; rw [contracted h hv,abs_of_nonneg hx.le]
lemma opposite : ∀ᶠ a:C G in 𝓝 0,lac (-a)=lac a:= by
   obtain ⟨Z,hZ⟩:= LocalH.actual G; have he:=real_ratio hZ
   have hT : Tendsto (fun x:C G=>-x) (𝓝 0) (𝓝 0):= by simpa using continuous_neg.tendsto (0:C G)
   filter_upwards [he,hT.eventually he,isOpen_ball.mem_nhds (mem_ball_self (x:=0) hZ.patch)] with a hx hy h; exact congr_arg Real.log (hy.symm.trans ((ratio_even hZ h).symm.trans hx))
lemma lac_pass (u:G.El)(a:C G): lac (G.adjoint u a)=lac a:= congr_arg Real.log (Primitives.HaarLogJets.spin_adjoint ..)
end YM.MS.Bare.Maurer
