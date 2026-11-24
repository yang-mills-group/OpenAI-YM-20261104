import YM.MSbar.Jade.Earful
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι]
variable (P:Matrix ι σ ℝ){C:Matrix σ σ ℝ} (hc:C.PosDef) {L x y a b u c r D:ℝ}
local notation "V"=> View σ
local notation "M"=> fieldLaw C
variable (h:∀ i:σ, C i i≤c) {n p:ℕ}
local notation "p!"=>PowerSeries.coeff
include h hc
noncomputable def boreo (i:ℕ)(c:ℝ)(p:ℕ):= 1+i*(2*Real.exp (c*(p:ℝ)^2/2))
noncomputable def maxVal (σ : Type)[Fintype σ](v:View σ)(p:ℕ) := (1+‖v‖)^p
lemma polMat (p:ℕ): Integrable (fun x: V=>(1+‖x‖)^p) (fieldLaw C) ∧ (∫ x:V,(1+‖x‖)^p∂fieldLaw C)≤ boreo (Fintype.card σ) c p:=by
   let g(i:σ)(x:V):=(1+|x i|)^p; let v(x:V):= 1+∑ i:σ,g i x; have he(x:V): (1+‖x‖)^p ≤ v x:=by
        by_cases hs:Nonempty σ; · obtain ⟨i,hi⟩:= Finset.exists_max_image Finset.univ (fun j=>|x j|) Finset.univ_nonempty; obtain ⟨hx,hQ⟩:=hi; have hp:‖x‖ ≤ |x i|:= (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j=> hQ j (mem_univ j); exact (pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x‖) (add_le_add_right hp _) p).trans ((Finset.single_le_sum (f:=fun j=>g j x) (fun i _=>by unfold g; positivity) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
        have hz: x=0 :=by funext i; exact False.elim (hs ⟨i⟩)
        rw [hz,norm_zero,add_zero,one_pow]; exact le_add_of_nonneg_right (sum_nonneg (fun j _=> False.elim (hs ⟨j⟩)))
   have hS(i:σ):= pol hc c h i p; have hK : Integrable (fun i:V=>∑ j,g j i) M:= integrable_finset_sum _ (fun i _=> hS i|>.1); let f(x:V):=(1+‖x‖)^p; have hp:Integrable v M:= (integrable_const 1).add hK; have hh:Integrable f M:= hp.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun i=> by unfold f; rw [Real.norm_of_nonneg (by positivity:0 ≤ (1+‖i‖)^p)]; exact he i)
   refine ⟨hh,(integral_mono hh hp he).trans ?_⟩; unfold v; rw [integral_add (integrable_const _) hK,integral_const,probReal_univ,one_smul,integral_finset_sum Finset.univ (fun i _=> hS i |>.1)]; unfold boreo; refine add_le_add_right ((sum_le_sum fun i _=> (hS i|>.2)).trans_eq ?_) _; rw [sum_const,nsmul_eq_mul,card_univ]
noncomputable def storm (i:ℕ)(b t c:ℝ):= i*(2*Real.exp (-(b*t) + c*b^2/2))
lemma skiesP (b t:ℝ)(hb:0 ≤ b)(ht:0≤ t): (fieldLaw C).real {v:View σ| t< ‖v‖} ≤ storm (Fintype.card σ) b t c:=by
    let X(i:σ):= {v:V| t< |v i|}; have hh(i): (fieldLaw C).real (X i)≤ 2*Real.exp (-(b*t) + c*b^2/2):=chorus hc c h i t b hb
    let Y:= {v:View σ| t<‖v‖}; have hp:Y⊆⋃ i:σ, X i:=by
        intro v h; by_contra he; rw [Set.mem_iUnion] at he; push Not at he; apply not_le_of_gt (show t < ‖v‖ from h); exact (pi_norm_le_iff_of_nonneg ht).mpr fun i=> le_of_not_gt (he i) -- not in
    refine (measureReal_mono hp).trans ((measureReal_iUnion_fintype_le _).trans ?_); refine (sum_le_sum (fun i _=> hh i)).trans_eq ?_;rw [sum_const,nsmul_eq_mul,card_univ];rfl
lemma spread (g: V →ℝ) (hm:Measurable g)(he:∀ x:View σ,|g x|≤ D*(1+‖x‖)^p)(hD:0≤D) : Integrable g M ∧ |∫ i:V,g i∂M|≤ D*boreo (Fintype.card σ) c p:=by
     obtain ⟨hx,ht⟩:= polMat hc h p; have hg := (hx.const_mul D).mono' (f:=g) hm.aestronglyMeasurable (Eventually.of_forall he); refine ⟨hg,(norm_integral_le_integral_norm g).trans ?_⟩; refine (integral_mono (μ:=M) hg.norm (hx.const_mul D) he).trans ?_; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ht hD
noncomputable def fish (i:ℕ)(p:ℕ)(c D ε s:ℝ):= ε*(D^2*boreo i c (2*p))+ s*ε⁻¹
lemma surf (g:View σ→ℝ)(Y:Set (View σ))(hY:MeasurableSet Y)(hu: (fieldLaw C).real Y≤ r)(hx:0 < b)(hh: Measurable g)(he:∀ z: View σ, |g z|≤ D*(1+‖z‖)^p)(hD:0 ≤ D): |(∫ i in Y,g i∂M)| ≤ fish (Fintype.card σ) p c D b r:=by
     obtain ⟨ht,hk⟩:= spread hc h g hh he hD; let f(z:View σ):=D*(1+‖z‖)^p; let H:(View σ)→ℝ:= fun z=> f z ^2; obtain ⟨hp,hP⟩:=polMat hc h (2*p); have hX(i):H i=D^2*(1+‖i‖)^(2*p):=by unfold H f;ring
     have h' : Integrable (fun z: View σ=> b * H z) M:=by simp_rw [hX]; exact ((hp.const_mul _).const_mul _)
     have hx':= inv_pos.mpr hx; let L(z:V):= b*H z+b⁻¹; have hy(z):‖g z‖≤ L z:=by
        have he :‖g z‖ ≤ f z:= he z; apply he.trans; apply le_of_mul_le_mul_left _ hx; unfold L H; rw [mul_add,mul_inv_cancel₀ hx.ne']; nlinarith only [sq_nonneg (1/2-b*f z)] -- 
     apply (show |∫ i in Y,g i∂M|≤ ∫ i in Y,‖g i‖∂M from norm_integral_le_integral_norm g).trans; apply (setIntegral_mono_on ht.integrableOn.norm (h'.integrableOn.add ((integrable_const (μ:=M) _).integrableOn)) hY (fun z _=>hy z)).trans; unfold fish; rw [integral_add' h'.integrableOn ((integrable_const (μ:=M) _).integrableOn), setIntegral_const]; refine add_le_add ?_ (mul_le_mul_of_nonneg_right hu hx'.le); apply le_trans (b:=∫ i,b*H i∂M); · rw [← integral_add_compl hY h']; apply le_add_of_nonneg_right; exact setIntegral_nonneg hY.compl (fun i _=>mul_nonneg hx.le (sq_nonneg (f i)))
     simp_rw [integral_const_mul, hX]; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (sq_nonneg _)) hx.le
end YM.MSbar.Lapaz
