import YM.SchemeRG11.Saddle.Rivet
import YM.SchemeRG11.Saddle.Loads
/-! All-order stationary coordinate bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SchemeRG11.Sway.Local
open Function Filter Set MeasureTheory Metric PertExtension.Series Radial Tested
open scoped Classical ContDiff Topology BigOperators NNReal
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F] [FiniteDimensional ℝ F]
lemma asp_mul {f:ℝ→ℝ}{a:ℕ→ℝ}(H:Aspiration f a)(c:ℝ): Aspiration (fun x=> c*f x) (fun i=> c*a i):=by
 intro n; obtain ⟨C,hC,h⟩:=H n
 refine ⟨‖c‖ * C,mul_nonneg (norm_nonneg _) hC,?_⟩
 filter_upwards [h] with t ht
 rw [Pi.sub_apply]; change ‖c*f t-peval _ n t‖≤_
 rw [show peval (fun i=>c*a i) n t=c*peval a n t from by unfold peval Zone.eval; simp only [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>mul_left_comm ..,← mul_sub,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

variable [MeasurableSpace E] [BorelSpace E][MeasurableSpace F] [BorelSpace F]
    (μ: Measure E)[μ.IsAddHaarMeasure](ν: Measure F)[ν.IsAddHaarMeasure]
def alpha (e:F≃L[ℝ]E):ℝ:= Measure.addHaarScalarFactor μ (ν.map e)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma alpha_pos(e:F≃L[ℝ]E):0<alpha μ ν e:=by unfold alpha; exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ (ν.map e)

/-- Change of variable in the fixed saddle with different real spaces/densities.
Needs only germ conditions, ConstantScale tracks jacobian trivializations in `e`.
No exchanges of formal series with nonformal maps. -/
lemma relocation {K f:E→ℝ}(hK: ContDiffAt ℝ ∞ K 0)(hf:Stationary f)(g:Goal f)
     {J k:F→ℝ}(hJ:ContDiffAt ℝ ∞ J 0)(hk:Stationary k)(j:Goal k)
     (e:F≃L[ℝ] E)(φ:F→E)(hp:ContDiffAt ℝ ω φ 0)(hφ:φ 0=0)(he:(fderiv ℝ φ 0).IsInvertible)
     (Hm:f ∘ φ=ᶠ[𝓝 0] k)(c:ℝ)(Hc:∀ᶠ x in 𝓝 0, K (φ x)*cost (e.symm.toContinuousLinearMap ∘L fderiv ℝ φ x)= c*J x):
    Radial.moment μ K f=fun i=>(alpha μ ν e*c)*Radial.moment ν J k i:=by
 obtain ⟨o,h,H⟩:=aurum_gain μ hK hf g
 obtain ⟨p,z,H'⟩:=aurum_gain ν hJ hk j
 obtain ⟨q,hq⟩:=he
 have hh: HasStrictFDerivAt φ q.toContinuousLinearMap 0:= hp.hasStrictFDerivAt' (by rw [hq]; exact (hp.differentiableAt (by simp)).hasFDerivAt) (by simp)
 let P := hh.toOpenPartialHomeomorph φ
 have hP: P.source∈𝓝 0:= P.open_source.mem_nhds hh.mem_toOpenPartialHomeomorph_source
 let W(x:F):= DifferentiableAt ℝ φ x ∧ x∈p ∧ x∈P.source ∧ φ x∈ o ∧ f (φ x)=k x ∧ K (φ x)*cost (e.symm.toContinuousLinearMap ∘L fderiv ℝ φ x)= c*J x
 have hw: ∀ᶠ x:F in 𝓝 0,W x:= ((hp.eventually (by simp)).mono (fun u hu=>hu.differentiableAt (by simp))).and ((show ∀ᶠ x:F in 𝓝 0,x∈p from z).and ((show ∀ᶠ x:F in 𝓝 0,x∈P.source from hP).and ((hp.continuousAt.eventually_mem (by rwa [hφ])).and (Hm.and Hc))))
 obtain ⟨r,hr,hw'⟩:= Metric.nhds_basis_closedBall.mem_iff.mp hw
 let T:= closedBall (0:F) r
 have ht:T∈𝓝 0:= closedBall_mem_nhds _ hr
 have hi: IsCompact T:= isCompact_closedBall ..
 have hM(x:F)(hx:x∈ T): W x:= hw' hx
 have ha: IsCompact (φ '' T):= hi.image_of_continuousOn fun x hx=> (hM x hx).1.continuousAt.continuousWithinAt
 have he:φ '' T∈𝓝 0:= Eq.subst (motive:=fun w=>φ '' T∈ w) ((hh.map_nhds_eq_of_equiv).trans (by rw [hφ])) (image_mem_map ht)
 have hu:= H (φ '' T) (by rintro _ ⟨x,hx,rfl⟩; exact (hM x hx).2.2.2.1) he ha
 have hv:= H' T (fun x hx=>(hM x hx).2.1) ht hi
 let U:=aurum μ K f (φ '' T)
 let ψ:= e.symm ∘ φ
 let M(t:ℝ)(y:E):= K y*Real.exp (-f y/t^2)
 have eq(t:ℝ): (∫ x in φ '' T, M t x ∂μ)=(alpha μ ν e*c)*(∫ u in T,J u*Real.exp (-k u/t^2) ∂ν):=by
    let C:= Measure.addHaarScalarFactor μ (ν.map e)
    have h : μ=C • (ν.map e):= Measure.isAddLeftInvariant_eq_smul ..
    have ht': MeasurePreserving e ν (ν.map e):= ⟨e.continuous.measurable,rfl⟩
    let X (u:F):= e.symm.toContinuousLinearMap ∘L fderiv ℝ φ u
    rw (occs := .pos [1]) [h]
    rw [Measure.restrict_smul,integral_smul_nnreal_measure] -- fix smul
    rw [show φ '' T= e '' (ψ '' T) from by rw [← image_comp]; congr 1; exact funext fun x=>(e.apply_symm_apply _).symm,ht'.setIntegral_image_emb (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding),integral_image_eq_integral_abs_det_fderiv_smul ν hi.measurableSet (f':=X) (fun x hx=>(e.symm.hasFDerivAt.comp _ (hM x hx).1.hasFDerivAt).hasFDerivWithinAt) (fun x hx y hy hij=> P.injOn (hM x hx).2.2.1 (hM y hy).2.2.1 (e.symm.injective hij)) (fun x=> M t (e x))]
    change ((C:ℝ)) * (∫ x in T,cost (X x)* M t (e (ψ x)) ∂ν)=_
    rw [mul_assoc,← integral_const_mul c]; apply congrArg (alpha μ ν e*·); apply setIntegral_congr_fun hi.measurableSet; intro x hx
    change cost (X x) * (M t (e (ψ x)))= _
    rw [show e (ψ x)= φ x from e.apply_symm_apply _]; unfold M; rw [(hM x hx).2.2.2.2.1,← mul_assoc,mul_comm (cost _) _, (hM x hx).2.2.2.2.2]; ring
 have eq': aurum μ K f (φ '' T)=fun t=> (alpha μ ν e*c)*aurum ν J k T t:=by
    funext t; unfold aurum; rw [eq,e.toLinearEquiv.finrank_eq,mul_left_comm]
 rw [eq'] at hu; exact hu.unique (asp_mul hv _)
end YM.SchemeRG11.Sway.Local
