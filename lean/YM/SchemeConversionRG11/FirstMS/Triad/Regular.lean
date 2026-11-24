import YM.SchemeConversionRG11.FirstMS.Triad.Touch

/-! Here the derivative distribution includes contacts. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

def ridge (a:Axis)(T:sheet):sheet:= fun q=> grad a (fun v=> T (q.1,v,q.2.2)) q.2.1

variable {R:ℝ} {T:sheet}

lemma Touch.gradient (h:Touch R T)(a:Axis):Touch R (ridge a T) := by
   refine ⟨h.inside,?_,?_,?_⟩
   · rintro z hz ⟨p,u⟩ hu
     change 0≤u at hu
     let f (x:ℂ × E4) := T (x.1,x.2,u)
     have hf:AH neighborhood f:= by
        refine upon_packed opened (isCompact_closedBall (0:E4) R) (fun z hz x hx => h.ends z hz (x,u) hu ?_) ?_ ?_
        · have ht:R<‖x‖:=lt_of_not_ge fun he=> hx (mem_closedBall.mpr (by simpa using he))
          change _<‖x‖^2+u
          exact lt_of_lt_of_le (pow_lt_pow_left₀ ht h.inside.le (by decide)) (le_add_of_nonneg_right hu)
        · intro x hx; exact (h.smooth (x.1,x.2,u) hx hu).comp (f:=fun p:ℂ×E4=> (p.1,p.2,u)) x (by fun_prop)
        intro z x hz; exact h.hol z hz (x,u) hu
     apply (hf.diff_smooth opened (0,basis a)|>.cr z p hz).congr_of_eventuallyEq
     filter_upwards [opened.mem_nhds hz] with z hz
     let g (v:E4):= (z,v)
     let L:= ContinuousLinearMap.inr ℝ ℂ E4
     have hg : HasFDerivAt g L p := by
        convert! ((hasFDerivAt_const (𝕜:=ℝ) z p).prodMk (hasFDerivAt_id p)) using 1
     have he := ((hf.smooth (z,p) hz).differentiableAt (by simp)).hasFDerivAt.comp (f:=g) p hg
     exact DFunLike.congr_fun he.fderiv _
   · intro x hx hp
     refine (ContDiffAt.fderiv (g:=fun p:ℂ×Patch=>p.2.1) (f:=fun p:ℂ×Patch=> fun v:E4=> T (p.1,v,p.2.2)) (x₀:=x) ?_ (by fun_prop) (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiffAt_const
     exact (h.smooth x hx hp).comp (f:=fun p:(ℂ×Patch) × E4=> (p.1.1,p.2,p.1.2.2)) (x,x.2.1) (by fun_prop)
   intro z hz p hp he
   have ht : (fun v:E4=> T (z,v,p.2))=ᶠ[𝓝 p.1] fun _=> 0 := by
      filter_upwards [((total_smooth.continuous.comp (continuous_id'.prodMk continuous_const)).continuousAt (x:=p.1)|>.tendsto).eventually (lt_mem_nhds he)] with v hv
      exact h.ends z hz (v,p.2) hp hv
   rw [ridge,grad,D,ht.fderiv_eq]; simp

def rotate (b:Bool)(i:Fin 3)(μ:Axis):ℂ→E4→ℝ→ℂ :=fun z=> lane z b i μ

def charge (R:ℝ) (A:ℂ→E4→ℝ→ℂ)(T:sheet)(z:ℂ) := ∫ t in Ioc 0 (4*R), billAt z (fun y=> servo A T (z,t,y))

/-- Analytic subgraph needs no poles; actual scale power
 λ^(4+2s - 3-2s -1)=1. -/
lemma funds (b:Bool)(i:Fin 3)(μ:Axis)(h:Touch R T){z:ℂ}(hz:z∈neighborhood) : AnalyticAt ℂ (charge R (rotate b i μ) T) z :=
   (bare_weight opened (mul_nonneg (by norm_num) h.inside.le) ((servo_ok (off_lane b i μ) h).integral opened)).analytic opened hz 0

/-- useful SO weight and Poisson tests. -/
lemma off_measured {F:ℂ→E4→ℝ→ℂ} (hF:Off F) {z:ℂ} (hz:z∈neighborhood) : Measurable (fun v:E4=> F z v 0) := by
   apply measurable_of_continuousOn_compl_singleton (a:= (0:E4))
   intro v hv
   have hp : v≠0:= hv
   have he : (v,(0:ℝ))∈ region := by
     simpa only [region,mem_setOf_eq,add_zero] using (pow_pos (norm_pos_iff.mpr hp) 2)
   exact ((hF.smooth z hz (v,0) he).continuousAt.comp (f:=fun v:E4=> (z,v, (0:ℝ))) (by fun_prop)).continuousWithinAt

lemma Touch.effective (h:Touch R T)(q:ℝ) (hq : 0 ≤ q) {z:ℂ} (hz:z∈neighborhood) : ContDiff ℝ ∞ (fun x:E4=> T (z,x,q)) :=
   contDiff_iff_contDiffAt.mpr fun x=> (h.smooth (z,x,q) hz hq).comp (f:=fun x:E4=>(z,x,q)) x (by fun_prop)

lemma Touch.supports (h:Touch R T){z:ℂ}(hz:z∈neighborhood)(u:ℝ)(hu:0≤u): HasCompactSupport (fun v=> T (z,v,u)):= by
    refine (isCompact_closedBall (0:E4) R).of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ isClosed_closedBall)
    intro v hv
    rw [mem_closedBall,dist_zero_right]
    exact le_of_not_gt fun he=> hv (h.ends _ hz (v,u) hu ((pow_lt_pow_left₀ he h.inside.le (by omega : (2:ℕ)≠0)).trans_le (le_add_of_nonneg_right hu)))

lemma capacitate (b:Bool)(i:Fin 3)(μ:Axis)(h:Touch R T) :
   let f (x:E4) := lane 0 b i μ x 0 * T (0,x,0)
   Integrable f ∧ charge R (rotate b i μ) T 0=∫ x,f x := by
   intro f
   let A:= rotate b i μ
   have H: Window neighborhood 1 (servo A T) := servo_ok (off_lane b i μ) h
   let c(x:ℝ × E4) := servo A T (0,x.1,x.2,0)
   have hg x : cap (‖x-0‖^2/(4*R)^2) • f x=f x:= by
      rcases le_or_gt ‖x‖ R with hr|hr
      · rw [sub_zero,cap_flat,one_smul]
        rw [abs_of_nonneg (by positivity),div_le_iff₀ (pow_pos (show 0<4*R from mul_pos (by norm_num) h.inside) 2)]
        nlinarith [pow_le_pow_left₀ (norm_nonneg x) hr 2]
      dsimp only [f]; rw [h.ends _ occurs (x,0) (by rfl) (show R^2<‖x‖^2+0 by rw [add_zero]; exact pow_lt_pow_left₀ hr h.inside.le (by decide)),mul_zero, smul_zero]
   have hu (t) (y:E4) (ht: 0<t) (hh:y≠0) : c (t,y) = t^3 • (lip (‖y‖^2) • f ((0:E4)+t • y)) := by
       have hp : (y,(0:ℝ))∈region:= show 0<‖y‖^2+0 by rw [add_zero]; exact pow_pos (norm_pos_iff.mpr hh) _
       have hb := owns_lane b i μ 0 occurs _ hp t ht
       have hw : ((↑t):ℂ)≠0:= by exact_mod_cast ht.ne'
       simp only [mul_zero, sub_zero, cpow_neg] at hb
       norm_num [cpow_ofNat] at hb
       simp only [c,servo,A,shape,swell,Q,total,f,rotate,Prod.smul_snd,Prod.smul_fst,smul_zero,hb,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero, vert,cpow_zero,one_mul,zero_add,real_smul,ofReal_pow]
       field_simp
   have hi : Integrable c (((volume:Measure ℝ).restrict (Ioc 0 (4*R))).prod volume) := by
       have he(t:ℝ×E4)(hp : |t.1| > 8*R+1 ∨ 1 < ‖t.2‖): c t=0:= by
          rcases hp with hp|hp
          · -- can ignore t using integrabilityOn product(Ioc × ball) dominator. use h to prove support.
            -- servo cut
            change vert 0*shape A 0 (t.2,0)*_ = 0
            by_cases hk : Q (t.2,0)<1/4
            · rw [shape,lip_flats (by rw [abs_of_nonneg (q_nonneg _)];exact hk), ofReal_zero,zero_mul,mul_zero,zero_mul]
            rw [h.ends _ occurs _ (sq_nonneg _) (show R^2 < Q (t.1 • (t.2,(0:ℝ))) from ?_),mul_zero]
            rw [q_scale]; apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (le_of_not_gt hk) (sq_nonneg _)); rw [← sq_abs t.1]; nlinarith only [hp,h.inside,sq_nonneg R,pow_lt_pow_left₀ hp (by linarith [h.inside] : 0≤8*R+1) (by decide : (2:ℕ)≠0)]
          exact H.ends _ occurs t.1 (t.2,0) (hp.trans_le (norm_fst_le (t.2,(0:ℝ))))
       let K:= closedBall (0:ℝ) (8*R+1) ×ˢ closedBall (0:E4) 1
       have hK : IsCompact K := IsCompact.prod (isCompact_closedBall ..) (isCompact_closedBall ..)
       refine ((H.AH'.slice occurs).1.continuous.comp (f:=fun x:ℝ×E4=>(x.1,(x.2,(0:ℝ)))) (by fun_prop))|>.integrable_of_hasCompactSupport ?_
       refine hK.of_isClosed_subset (isClosed_tsupport c) (closure_minimal (fun x hx=> ?_) hK.isClosed)
       have he := not_or.mp (fun h=> hx (he _ h)); exact ⟨mem_closedBall.mpr (by simp only [dist_zero_right,Real.norm_eq_abs]; exact le_of_not_gt he.1),mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_not_gt he.2)⟩
   have hm : Measurable f:= (off_measured (off_lane b i μ) occurs).mul (h.effective 0 (by rfl) occurs).continuous.measurable
   have hN:= near_part (x:=0) (T:=curry c) (mul_pos (by norm_num) h.inside) hm (fun t ht=> volume.ae_ne 0|>.mono fun y hy=> hu t y ht.1 hy) hi
   simp_rw [hg] at hN
   refine ⟨hN.1,(Eq.trans ?_ hN.2.symm)⟩
   exact integral_congr_ae (μ:=volume.restrict _) (Eventually.of_forall fun t=> H.zero t occurs)

end YM.SchemeConversionRG11.FirstMS.Triad
