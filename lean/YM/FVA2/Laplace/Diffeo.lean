import YM.FVA2.Laplace.Window
import YM.FVA2.Orbit.Metered
/-!
# Moment comparison lemma under a nonlinear chart change

Determinant relative to `L` (`θ'(0)=L`), positivity fixed locally. Explicit discarded scalar
factor from the two choices of tangent Haar laws; never forced to one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Laplace
open Function Set Filter Metric MeasureTheory Measure PertExtension Series Radial Series.Tested ContinuousLinearMap
open Orbit
open scoped ContDiff Topology Classical BigOperators
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {θ:E→F} {L : E ≃L[ℝ] F}
structure Jacobs (θ:E→F)(L:E≃L[ℝ] F) : Prop where
 analytic : ContDiffAt ℝ ω θ 0
 origin : θ 0=0
 equiv : fderiv ℝ θ 0=L.toContinuousLinearMap
namespace Jacobs
set_option linter.unusedSectionVars false -- uniform ctx for both finite geometric spaces & Jacobs
variable (x:Jacobs θ L)
include x
local notation "D" => fderiv ℝ θ
local notation "J" => fun y=> meter L (D y)
lemma forwards : Tendsto θ (𝓝 0) (𝓝 0) := Orbit.aimed (x.analytic.continuousAt) x.origin
lemma strict : HasStrictFDerivAt θ L.toContinuousLinearMap 0:= x.equiv ▸ x.analytic.hasStrictFDerivAt (by simp)
lemma meter_hot : ContDiffAt ℝ ω (J) 0:= Orbit.meter_map L (x.analytic.fderiv_right (by simp))
lemma pos : ∀ᶠ y:E in 𝓝 0,0< meter L (D y):= x.meter_hot.continuousAt.eventually (isOpen_Ioi.mem_nhds (show 0<meter L (D 0) from by rw [x.equiv,meter_self]; positivity))
variable {f:F→ℝ}
omit x [FiniteDimensional ℝ F] in
lemma fderiv_flat (p:Steep f) : fderiv ℝ f 0=0:= ContinuousLinearMap.ext (fun v=>by have he:= p.base1 v; simp only [jet,Nat.factorial_one,Nat.cast_one,inv_one,one_mul,iteratedFDeriv_one_apply] at he; exact he)
lemma jet2 (p:Steep f) (u:E): jet (f ∘ θ) 2 u= jet f 2 (L u):= by
 let F':= fderiv ℝ f; let C:=F' ∘ θ; have hf:=p.smooth; have ht:DifferentiableAt ℝ θ 0:= x.analytic.differentiableAt (by simp); have hv:DifferentiableAt ℝ F' (θ 0):= x.origin.symm ▸ ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp));
 have hF:(F' ∘ θ) 0=0:= by rw [Function.comp_apply,x.origin]; exact fderiv_flat p
 have he: fderiv ℝ (f ∘ θ)=ᶠ[𝓝 0] (fun x=> C x ∘L D x):= by
    filter_upwards [x.analytic.eventually (by simp), x.forwards.eventually ((hf.of_le (show (1:WithTop ℕ∞)≤ ∞ from by simp)).eventually (by simp))] with y hx hy using fderiv_comp y (hy.differentiableAt (by simp)) (hx.differentiableAt (by simp))
 unfold jet; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply, he.fderiv_eq, fderiv_clm_comp (hc:=hv.comp 0 ht) ((x.analytic.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)), hF, fderiv_comp 0 hv ht, x.origin, x.equiv, map_zero,zero_comp,zero_add]; rfl
lemma steepens (p:Steep f) : Steep (f ∘ θ):= by
 have hf : ContDiffAt ℝ ∞ f (θ 0):= x.origin.symm ▸ p.smooth; refine ⟨⟨hf.comp 0 (x.analytic.of_le le_top),by rw [Function.comp_apply,x.origin,p.base0],fun u=>?_⟩,?_⟩
 · simp only [jet,iteratedFDeriv_one_apply]; rw [fderiv_comp (0:E) (hf.differentiableAt (by simp)) (x.analytic.differentiableAt (by simp)), x.origin, fderiv_flat p,zero_comp,_root_.zero_apply,mul_zero]
 apply quadratic_min; intro y hy; rw [x.jet2 p]
 obtain ⟨c,hc,h⟩:=p.gap; exact lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.mpr (fun hn=>hy (L.injective (hn.trans L.map_zero.symm)))) _)) (h _)

omit x
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure]
local notation "μₑ" => map L μ
local notation "d" => Module.finrank ℝ E
-- exact scalar, independent of probe, between picked Haar measures once leading center fixed

def amount (L:E≃L[ℝ] F)(μ:Measure E)[μ.IsAddHaarMeasure](ν:Measure F)[ν.IsAddHaarMeasure] : ℝ := (addHaarScalarFactor (μ.map L) ν).val
lemma pay_pos : 0<amount L μ ν:= addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
lemma rate (S:Set F)(g:F→ℝ) : (∫ y in S,g y ∂(Measure.map L μ))= amount L μ ν * ∫ y in S,g y ∂ν:= by
 let k:= addHaarScalarFactor (μ.map L) ν; rw [show μ.map L=k • ν from isAddLeftInvariant_eq_smul _ _, restrict_smul, integral_smul_nnreal_measure]; rfl
variable {S:Set E} {f₀ K:E→ℝ} {K':F→ℝ}
-- theorem with scalar
include x
lemma on_window (p:IsOpen S)(h: ∀ y∈S, DifferentiableAt ℝ θ y ∧ meter L (D y)≥0 ∧ K y= meter L (D y) * K' (θ y) ∧ f₀ y=f (θ y))(ht:InjOn θ S): reading μ S K f₀=(amount L μ ν) • reading ν (θ '' S) K' f:= by
    let A:= L '' S; have hZ:IsOpen A:= L.toHomeomorph.isOpenMap S p; let g:=θ ∘ L.symm; have hg:g '' A=θ '' S:= by rw [image_image]; congr; ext y; exact congr_arg θ (L.symm_apply_apply _)
    have hK : InjOn g A:= by
       intro y hy z hz hh; obtain ⟨y,hy,rfl⟩:=hy; obtain ⟨z,hz,rfl⟩:=hz; simp only [g,Function.comp_apply,L.symm_apply_apply] at hh; exact congr_arg L (ht hy hz hh)
    let M (z:F):= (D (L.symm z)) ∘L L.symm.toContinuousLinearMap; have hm(z:F)(hz:z∈A): HasFDerivWithinAt g (M z) A z:= by
       refine ( HasFDerivAt.comp z ((h (L.symm z) ?_).1.hasFDerivAt) L.symm.hasFDerivAt).hasFDerivWithinAt; obtain ⟨x,hx,rfl⟩:=hz; rw [L.symm_apply_apply]; exact hx
    funext t; let w:=envelope K' f t; let k:=envelope K f₀ t; let a:=fun y=> |(M y).det| • w (g y); let e:= L.toHomeomorph.toMeasurableEquiv; have he:e ⁻¹' A=S:= by change L ⁻¹' A=S; exact L.injective.preimage_image S
    have hr: amount L μ ν * (∫ y in θ '' S,w y ∂ν)=∫ x in S, k x ∂μ:= by
       rw [← rate μ ν,←hg, integral_image_eq_integral_abs_det_fderiv_smul (μ.map L) hZ.measurableSet hm hK]; change (∫ y in A,a y ∂(μ.map e))=_; rw [setIntegral_map_equiv, he]; apply setIntegral_congr_fun p.measurableSet; intro x hx
       obtain ⟨_,hb,hf,hg⟩:= h x hx
       change a (L x)= envelope K f₀ t x; unfold a w g M; rw [Function.comp_apply,L.symm_apply_apply]; rw [show (D x ∘L L.symm.toContinuousLinearMap).det=_ from rfl]; change |meter L (D x)| * _= _; unfold envelope; rw [abs_of_nonneg hb,hg,hf,mul_assoc]
    change (t^d)⁻¹ * _= _ * ((t^(Module.finrank ℝ F))⁻¹ * _); rw [←L.toLinearEquiv.finrank_eq,mul_left_comm, ←hr]

-- finite-dimensional coefficient invariance, not uniform estimates
local instance : CompleteSpace E:= FiniteDimensional.complete ℝ _
omit x [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] μ in
private lemma priced {A:ℝ→ℝ}{β:ℕ→ℝ}(a:ℝ)(h:Tested.Aspiration A β): Tested.Aspiration (a • A) (a • β):= by
 intro n; obtain ⟨C,hc,H⟩:=h n; refine ⟨|a| *C,by positivity,?_⟩; filter_upwards [H] with t ht
 have he : peval (a • β) n t= a* peval β n t:= by unfold peval Zone.eval; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; change _* (a*β i)=a * (_*β i);ring
 change ‖a*A t - peval (a • β) n t‖ ≤ _; rw [he,←mul_sub,norm_mul,mul_assoc,Real.norm_eq_abs a]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
theorem moment_change (p:Steep f)(hf: f₀=ᶠ[𝓝 0] (f ∘ θ))(hp:ContDiffAt ℝ ∞ K' 0)(hk: ∀ᶠ y in 𝓝 0,K y= meter L (D y) * K' (θ y)): moment μ K f₀=amount L μ ν • moment ν K' f:=by
 obtain ⟨U,hu,hU⟩:= on_patch μ ((x.steepens p).germ hf.symm) (K:=K) (((x.meter_hot.of_le le_top).mul ((x.origin.symm ▸ hp : ContDiffAt ℝ ∞ K' (θ 0)).comp 0 (x.analytic.of_le le_top))).congr_of_eventuallyEq hk)
 obtain ⟨A,ha,hA⟩:= on_patch ν p hp
 let e:= x.strict.toOpenPartialHomeomorph θ (f':=L); have he:(0:E)∈ e.source:= HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source x.strict
 have hg : ∀ᶠ u:E in 𝓝 0, u∈e.source := e.open_source.mem_nhds he
 obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp ( (show ∀ᶠ x:E in 𝓝 0,x∈U from hu).and ((x.forwards.eventually (show ∀ᶠ y:F in 𝓝 0,y∈A from ha)).and (hg.and ((x.analytic.eventually (by simp)).and (hf.and (hk.and x.pos))))))
 let S:= ball (0:E) r; have hS:S∈𝓝 0:= ball_mem_nhds _ hr; have hse:S⊆e.source:= fun y hy=>(h hy).2.2.1
 obtain hj:= hU S hS (isOpen_ball.measurableSet) (fun y hy=> (h hy).1); have hT:IsOpen (θ '' S):= e.isOpen_image_of_subset_source isOpen_ball hse
 have heq:= x.on_window μ ν (S:=S) isOpen_ball (fun y hy=> ⟨(h hy).2.2.2.1.differentiableAt (by simp), (h hy).2.2.2.2.2.2.le,(h hy).2.2.2.2.2.1,(h hy).2.2.2.2.1⟩) (e.injOn.mono hse)
 rw [heq] at hj; have hp:= hA (θ '' S) (x.origin ▸ (e.image_mem_nhds he hS : θ '' S∈ 𝓝 (θ 0))) hT.measurableSet (image_subset_iff.mpr (fun y hy=> (h hy).2.1))
 exact hj.unique (priced _ hp)
end Jacobs
end YM.FVA2.Laplace
