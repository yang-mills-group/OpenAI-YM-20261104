import YM.AlbaMS.Inlay.Link
import YM.AlbaMS.Nexus.Shifts

/-! # Complete Panel in native chart -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {G : Gauge} {V I J R : Type*}
variable (Ω:Net V I) [Fintype V] [Fintype I] {P:ChartRatio G}(hp:LocalRatio P)
def scent (P: ChartRatio G) (x:ink G V):= ∑ e:V, stud P (x e)
omit [Fintype I] in
lemma scent_zero (hp:LocalRatio P) : scent (V:=V) P 0=0:=by exact Finset.sum_eq_zero fun _ _=> lilt hp
lemma natJ (hp:LocalRatio P) {x:ink G V}(h:∀ i, x i∈ Metric.ball 0 P.radius): ContDiffAt ℝ ω (scent P) x := ContDiffAt.sum (fun i _=> ContDiffAt.comp (g:=stud P) (f:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=> G.Color) i) x (Quill.lit hp _ (h i)) (contDiffAt_apply ..))
def fragrant (hp:LocalRatio P): Grove (ink G V):= ⟨scent P,natJ hp (fun _=>Metric.mem_ball_self hp.patch)⟩ -- no need I
omit [Fintype I] in
lemma weightless (j:Flit G I): (∑ i:Flit G V, DA i (Ω.chat j i)) = -impulse Ω.chat j (bare (fragrant (V:=V) hp)):=by
  let C:=pathof G V I; let Y:=slabQ j; let F:Grove (ink G V):= fragrant hp
  rw [waters Ω F _ (ray Ω Y F) (Filter.EventuallyEq.refl ..)]
  have ht i : DA i (Ω.chat j i)= C.shine (dx (slabQ i) (Ω.spotG j i)):=rfl
  simp_rw [ht]
  have he (i:V) : ∀ᶠ x:ink G V in 𝓝 0,x i ∈ Metric.ball 0 P.radius:= ((continuous_apply i).tendsto (0:ink G V)).eventually (Metric.ball_mem_nhds _ hp.patch)
  let U:Grove (ink G V):= (-1:ℝ) • (Ω.ray Y F)
  have hl : U.val=ᶠ[𝓝 0] ∑ i:Flit G V,(dx (slabQ i) (Ω.spotG j i)).val:=by
    filter_upwards [eventually_all.mpr he, tide (G:=G) (V:=V)] with x hx H
    let W:= Ω.fly Y x; let N (i:V):=(fderiv ℝ (fun v=> arch v (Ω.coast i Y)) (x i)).toLinearMap
    let E i:= fderiv ℝ (stud P) (x i) (W i)
    have hg (i:Flit G V) : (dx (slabQ i) (Ω.spotG j i)).val x = coefQ i.2 (N i.1 (base G i.2)):=by
      change fderiv ℝ ((stip i).toContinuousLinearMap ∘ Ω.fly Y) x _= _; rw [fderiv_comp _ (stip i).toContinuousLinearMap.differentiableAt ((Ω.wax_rate H Y).differentiableAt (by simp)),(stip i).toContinuousLinearMap.fderiv]; change coefQ i.2 ((fderiv ℝ (Ω.fly Y) x (slabQ i)) i.1)=_; rw [Ω.sees H,  show slabQ i i.1= _ from slab i.1 i.2 i.1, if_pos rfl]; rfl
    have Hs : fderiv ℝ (scent P) x W=∑ i:V,E i:=by
      let L (i:V) := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=> G.Color) i
      have hU i : HasFDerivAt (stud P ∘ L i) ((fderiv ℝ (stud P) (x i)).comp (L i)) x:= (((Quill.lit hp _ (hx i)).differentiableAt (by simp)).hasFDerivAt.comp x (L i).hasFDerivAt)
      rw [show fderiv ℝ (scent P) x=_ from (HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=> hU i)).fderiv, _root_.sum_apply]; rfl -- fix
    have HH (i:V): -E i= ∑ j:G.ColorIndex, coefQ j (N i (base G j)):=by
      have he: trace ℝ _ (N i)+E i=0:= Quill.divergence (H i) hp (hx i) (Ω.coast i Y); rw [← eq_neg_iff_add_eq_zero] at he; rw [← he]; rw [trace_eq_matrix_trace ℝ (base G).toBasis (N i), Matrix.trace]; simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,(base G).coe_toBasis_repr_apply, (base G).repr_apply_apply, (base G).coe_toBasis,coef_inner]
    rw [Finset.sum_apply]; change (-1:ℝ) * fderiv ℝ (scent P) x W=_; rw [Hs,neg_one_mul,← Finset.sum_neg_distrib]; simp_rw [hg,HH,Fintype.sum_prod_type] -- sum_type progress
  change _= - C.shine (Ω.ray Y F); rw [← neg_one_smul ℝ (C.shine _),← Brook.gleam_smul]; exact (C.flash _ _ _ hl).symm

-- physical invariant operator/action entry. Comes from local genuine group integrand:
structure Luster (Ω : Net V I)(G:Gauge)[Fintype V] where
  integrand : (V→G.El)→ ℝ
  smooth : Queue (fromWax integrand)
  solid : Ω.Honor integrand
namespace Luster
variable {Ω} (F:Luster Ω G) {hp}
def caseG : Grove (ink G V):= ⟨fromWax F.integrand,F.smooth⟩
omit [Fintype I] in
lemma calm (j:Flit G I): impulse Ω.chat j (bare F.caseG)=0:=by
  let g := Ω.ray (slabQ j) F.caseG
  rw [waters Ω _ _ g (Filter.EventuallyEq.refl ..)]; refine (pathof G V I).vanish g ?_
  filter_upwards [tide (G:=G) (V:=V), F.caseG.2.eventually (by simp)] with A hh hF
  let X:= Ω.fly (slabQ j) A; let S (e:V):= Ω.coast e (slabQ j)
  let Vt (t:ℝ)(e:V):= warp t (S e) (G.lieExp (A e)); let u (t:ℝ): ink G V := fun e=> snap G (Vt t e)
  have he : u 0=A:= funext fun i=> by rw [show u 0 i=snap G (Vt 0 i) from rfl,show Vt 0 i=G.lieExp (A i) from warp_zero ..]; exact (hh i).permit
  have hu : HasDerivAt u X 0 := hasDerivAt_pi.mpr fun i=> delta_p _ (hh i)
  have hx i : ∀ᶠ t:ℝ in 𝓝 0,G.lieExp (u t i)= Vt t i:=by
    obtain ⟨U,s,h,H⟩:= hh i
    have ht : Continuous fun t=> Vt t i:=by unfold Vt warp; fun_prop
    filter_upwards [ht.continuousAt (x:=0) (h.1.mem_nhds (show Vt 0 i∈U by rw [show Vt 0 i=_ from warp_zero ..]; exact h.2.2.2.2.2.1 H))] with t ht; exact h.2.2.2.1 ht
  change fderiv ℝ _ A X=0
  refine HasDerivAt.unique ((show HasFDerivAt F.caseG.val _ (u 0) by rw [he]; exact (hF.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hu) ((hasDerivAt_const (0:ℝ) (F.caseG.val A)).congr_of_eventuallyEq ?_)
  filter_upwards [eventually_all.mpr hx] with t hv; change F.integrand (_∘_)=_; rw [show G.lieExp ∘ u t= Vt t from funext hv, show Vt t= _ from warped Ω t A (slabQ j)]; exact F.solid _ _ -- Vt not expands into home
lemma panel (hp:LocalRatio P): Panel (grit G I) Ω.chat (bare F.caseG) (bare (V:=V) (fragrant hp)):=
  ⟨fun _ _=>bare_h _,fun _ _=> bare_simple _, bare_h _,bare_simple _,bare_h _,bare_simple _,wade Ω,F.calm, weightless Ω hp⟩
end Luster
end YM.MSBar.Inlay.Net
