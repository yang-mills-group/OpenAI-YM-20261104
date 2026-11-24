import YM.OPE.Compatible.Chain.Mesh
/-!
# Gaussian charge operations tying Feynman flight extraction to tile Wick even with singular colors
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Lattice Laurent Tree Woody Weir Cascade MeasureTheory Exterior Bloch Matrix Spectral
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace
open RG Bid PertExtension Series Asymptotics MSbar.Tree Further.FreeCovariance.KP GaussianScore Metric
variable {E I:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
abbrev Dual' (E:Type*)[AddCommGroup E][Module ℝ E]:= Module.Dual ℝ E
protected lemma slopeShape (P:E→ₗ[ℝ] Dual' E) : Continuous (fun x=> P x x):=by
     let L: Dual' E≃ₗ[ℝ] (E →L[ℝ] ℝ):= LinearMap.toContinuousLinearMap
     let Y:= (L.toLinearMap.comp P).toContinuousLinearMap; exact Y.continuous.clm_apply continuous_id
lemma getsSlope (P:E→ₗ[ℝ] Dual' E)(h:∀ x,x≠0→0<P x x) : ∃ c>0,∀ x,c*‖x‖^2 ≤ P x x/2:=by
    let s:=sphere (0:E) 1; by_cases he:Set.Nonempty s
    · let f:E→ℝ:= fun x=>P x x/2; obtain ⟨x,hx,hp⟩:= (isCompact_sphere ..).exists_isMinOn he (((Libra.slopeShape P).div_const _).continuousOn)
      have ht:x≠0:=fun w=>by simp [w] at hx
      refine ⟨f x,div_pos (h _ ht) (by norm_num),fun y=>?_⟩; by_cases hy:y=0; · subst y;simp
      let u: E := ‖y‖⁻¹ • y; have hu:0< ‖y‖:= norm_pos_iff.mpr hy; have hv:u ∈ s:=by simp [s,u,hy,norm_smul]
      have hg: ‖y‖ • u=y:= smul_inv_smul₀ hu.ne' _
      calc
          _ ≤ f u*‖y‖^2:= mul_le_mul_of_nonneg_right (hp hv) (by positivity)
          _ = _:=by change (P u u / 2) * ‖y‖^2=_; nth_rw 2 3 [← hg]; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul];ring
    refine ⟨1,zero_lt_one,fun x=>?_⟩; by_cases h:x=0
    · subst x; simp
    exact (he ⟨‖x‖⁻¹ • x,by simp [s,h,norm_smul]⟩).elim
protected def giraffe (P:E→ₗ[ℝ] Dual' E)(hh:∀ x y,P x y=P y x)(h:∀ x,x≠0→0<P x x): Law E:=⟨P,hh,getsSlope P h,Libra.slopeShape P⟩
-- construct P bilinear separately
omit [FiniteDimensional ℝ E] in lemma giraffe_addendum {f:E→E→ℝ}(h:∀ i,∃ A:Dual' E,f i=A) (he:∀ x y,f x y=f y x):∃ A:E→ₗ[ℝ] Dual' E,∀ x y,A x y=f x y:=by
     choose a ha using h; have ht(x y): f x y=a x y:=congr_fun (ha x) y
     have hp(x y): a x y=a y x:= (ht x y).symm.trans ((he x y).trans (ht y x)); refine ⟨{toFun:=a,map_add':=fun x y=> LinearMap.ext fun z=> by simp only [LinearMap.add_apply,hp _ z,map_add],map_smul':=fun c x=> LinearMap.ext fun z=>by simp only [LinearMap.smul_apply,RingHom.id_apply,hp _ z,map_smul]},fun i j=>(ht i j).symm⟩
-- linear equivalence with W translated chart.
variable [MeasurableSpace E][BorelSpace E]
end YM.OPE.Libra
