import YM.FormalBulk08.Annex.Ports
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Dawn Set MeasureTheory
open scoped BigOperators Topology ENNReal Classical ContDiff
variable {D k:ℕ}
abbrev Boom := C(Deck,ℝ)

def clipL (x:E4)(i: Axis): ℝ:= max (-1/2) (min (1/2) (x i))
def caulk (x:Pier) : Deck:= ⟨WithLp.toLp 2 (clipL x.val),cube_test.mpr (fun i=>abs_le.mpr (by change -((1:ℝ)/2)≤clipL x.val i ∧ clipL x.val i≤1/2; refine ⟨Eq.trans_le (by rw [neg_div]) (le_max_left ..), max_le (by norm_num) (min_le_left ..)⟩))⟩
lemma clipped : Continuous caulk:= by
   refine Continuous.subtype_mk ((PiLp.continuous_toLp _ _) |>.comp (continuous_pi fun i:Axis=> continuous_const.max (continuous_const.min ((shadeP i).continuous.comp (continuous_subtype_val (p:=fun p:E4=> p∈ Metric.closedBall 0 8)))))) _
lemma grip (x:Deck): caulk (embark x)=x:= by
   apply Subtype.ext;apply PiLp.ext; intro i; obtain ⟨he,hp⟩:= abs_le.mp (cube_test.mp x.property i); change clipL x.val i=_;unfold clipL;rw [min_eq_right hp,neg_div,max_eq_right he]
def jacket : Hub→L[ℝ] Boom:= LinearMap.mkContinuous (σ:=RingHom.id ℝ) {
    toFun f:= f.comp (⟨embark,embarks⟩: C(Deck,Pier))
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl } 1 (fun x=>by rw [one_mul]; exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun v=>x.norm_coe_le_norm (embark v)))
lemma oil: ‖jacket‖≤1:= ContinuousLinearMap.opNorm_le_bound jacket zero_le_one (fun x=>by rw [one_mul]; exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun v=>x.norm_coe_le_norm (embark v)))
lemma pressed (μ:Measure Pier)(x:Boom) : (∫ t,x t ∂(μ.map caulk))=∫ t,x (caulk t) ∂μ := integral_map clipped.measurable.aemeasurable x.continuous.aestronglyMeasurable
lemma cairo (μ:Measure Pier) [IsFiniteMeasure μ]: IsFiniteMeasure (μ.map caulk):= inferInstance
lemma calve (μ:Measure Pier): (μ.map caulk).real univ=μ.real univ := by simp [measureReal_def,Measure.map_apply clipped.measurable]
lemma radial (G:Boom→L[ℝ]ℝ) :∃ μ ν:Measure Deck,IsFiniteMeasure μ ∧ IsFiniteMeasure ν∧ μ.real univ+ν.real univ≤ ‖G‖ ∧ ∀ x:Boom,G x=(∫ t,x t ∂μ)- ∫ t,x t ∂ν:= by
   obtain ⟨μ,ν,H,U,J,P⟩:=dual_ferns (G.comp jacket); refine ⟨μ.map caulk,ν.map caulk,cairo μ,cairo ν,?_,fun x=>?_⟩
   · rw [calve,calve,J];exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) oil)
   rw [pressed,pressed]; let f := x.comp (⟨caulk,clipped⟩ : C(Pier,Deck)); have h: jacket f=x:=ContinuousMap.ext fun i=> DFunLike.congr_arg x (grip i); exact (congr_arg G h.symm).trans (P f)
lemma pole (D:ℕ)(B:ℝ)(he:0≤B)(f:Studio D→ₗ[ℝ]ℝ)(h:∀ x,‖f x‖≤ B*‖compress D x‖): ∃ μ ν: Brush D→Measure Deck, (∀ i,IsFiniteMeasure (μ i))∧(∀ i,IsFiniteMeasure (ν i)) ∧ (∑ i,((μ i).real univ +(ν i).real univ)) ≤ Fintype.card (Brush D)*B ∧∀ p:Studio D,f p=∑ i,((∫ t,(compress D p) i t ∂(μ i)) - ∫ t,(compress D p) i t ∂(ν i)):= by
   let F:=(compress D).rangeRestrict; obtain ⟨R,H⟩:=F.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (LinearMap.surjective_rangeRestrict _)); have he' x:F (R x)=x:=LinearMap.congr_fun H x
   have hx(x:Studio D): f (R (F x))=f x:= by
       have hq: F (R (F x) - x)=0:=by rw [map_sub,he',sub_self]
       have hp:compress D (R (F x)-x)=0:=Subtype.ext_iff.mp hq
       have hz:=h (R (F x)-x); rw [map_sub,hp,norm_zero,mul_zero,norm_le_zero_iff] at hz; exact sub_eq_zero.mp hz
   obtain ⟨L,p,hL⟩:= offsets _ (f.comp R) B he (fun x=>by nth_rw 2 [←he' x];exact h (R x))
   let g i:=ContinuousLinearMap.single ℝ (fun _:Brush D=>Boom) i; choose μ ν hμ hν hZ P using fun i=> radial (L.comp (g i))
   refine ⟨μ,ν,hμ,hν,?_,fun x=>?_⟩
   · refine le_trans (Finset.sum_le_sum (g:=fun _=>B) fun i _=>?_ ) ?_
     · exact (hZ i).trans (le_trans ((ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_single_le_one ..))) hL)
     simp
   simp_rw [←P]; have hp:compress D x=∑ i,g i (compress D x i):=(Finset.univ_sum_single _).symm
   exact (hx x).symm.trans ((p (F x)).symm.trans ((congr_arg L hp).trans (map_sum L ..)))
end YM.FormalBulk08.Annex
