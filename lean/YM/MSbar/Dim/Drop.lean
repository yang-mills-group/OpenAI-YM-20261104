import YM.MSbar.Dim.Wide

/-! Integrate one extra ordinary plane before/after the dimensionally normalized operation.
Work temporarily with large positive real part of the dimensional parameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical NNReal
variable {H U v : ℝ} {F : Plane × ℝ → ℂ} {f : ℝ → ℂ}
local notation "π" => Real.pi
lemma pair_density (g : ℝ → ℂ) : (∫ a : Plane,g (‖a‖^2)) = (↑π:ℂ)*(∫ u in Ioi 0,g u):=by
   have he : Module.finrank ℝ Plane=2:=by simp
   have hp := MeasureTheory.integral_fun_norm_addHaar (volume : Measure Plane) (fun a=> g (a^2))
   have ht : volume.real (ball (0:Plane) 1)=π:=by rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (hat_dim 1)]; norm_num [Real.pi_pos.le] -- pi notation
   have hv:= integral_comp_rpow_Ioi_of_pos (g:=g) (zero_lt_two (α:=ℝ)); norm_num [ht] at hp; norm_num [Real.rpow_two] at hv
   simp_rw [mul_assoc] at hv; rw [integral_const_mul] at hv; rw [hp,← hv]; ring
section
variable (hf : Radius H f)
variable (hH : HasTemperateGrowth F) (hF : ∀ a:Plane, Radius H fun r=>F (a,r))
variable (he : ∀ x t, F (x,t)=f (Real.sqrt (‖x‖^2+t^2)))
include hf he hF hH

omit he hf in
lemma drop_analytic {K : Set Plane} (hK : IsCompact K) (t : ℂ→ℂ) (ht : Differentiable ℂ t) (z : ℂ) : AnalyticAt ℂ (fun z=> ∫ v in K,radial (fun r=> F (v,r)) (t z)) z:=by
   let G:=fun p:ℂ × (ℝ × Plane) => radial (fun r=> F (p.2.2,r)) (t p.1)
   have hR : AH univ (fun q:ℂ×Plane=> radial (fun r=>F (q.2,r)) (t q.1)):=radial_AH (X:=Plane) (F:=fun p=> F p.2) ht.differentiableOn isOpen_univ (AH.param_tame hH) (fun _ _ v=> hF v)
   have h : AH univ G:= by unfold G; exact AH.arguments (w:=Prod.snd) (Y:=ℝ×Plane) hR (tame_projR (X:=ℝ) (Y:=Plane))
   haveI : IsFiniteMeasure (volume.restrict K):= ⟨by rw [Measure.restrict_apply_univ];exact hK.measure_lt_top⟩
   have hh:= (h.after_average (μ:=volume.restrict K) (p:=id) (integrable_const (1:ℂ)) aestronglyMeasurable_id (ae_restrict_mem hK.measurableSet) hK).analytic isOpen_univ (mem_univ z) 0
   simpa [id,G] using hh
omit hH in
lemma raised_both (hv : 0<v) (a : Plane) : raised (fun r=> F (a,r)) (Real.sqrt v)= raised f (Real.sqrt (‖a‖^2+v)):= by
   have hx : (fun u=>F (a,Real.sqrt u)) =ᶠ[𝓝 v] fun u=> f (Real.sqrt (‖a‖^2+u)) := by
       filter_upwards [lt_mem_nhds hv] with s hs; rw [he,Real.sq_sqrt hs.le]
   have hs:= (sqrt_deriv hf (show 0< ‖a‖^2+v from by positivity)).scomp (h:=fun v:ℝ=> ‖a‖^2+v) v ((hasDerivAt_const v _).add (hasDerivAt_id' v))
   simp only [zero_add,one_smul] at hs
   exact (sqrt_deriv (hF a) hv).unique (hs.congr_of_eventuallyEq hx)
omit he hH hF in
lemma eat_s (hv : 0<v) : (∫ w:Plane, raised f (Real.sqrt (‖w‖^2+v))) = -(↑π:ℂ)* f (Real.sqrt v) := by
   rw [pair_density (fun u=>raised f (Real.sqrt (u+v)))]
   let L:= H^2+1; let g(x:ℝ):=f (Real.sqrt (x+v)); let d(x:ℝ):=raised f (Real.sqrt (x+v)); have he :Continuous d:=(hf.raising.smooth.continuous.comp Real.continuous_sqrt).comp (continuous_id.add continuous_const)
   have hL : 0 ≤ L:= by unfold L; positivity
   have hg : Continuous g:=(hf.smooth.continuous.comp Real.continuous_sqrt).comp (continuous_id.add continuous_const)
   have ht(v':ℝ)(hi:v'∈ Ioo 0 L): HasDerivAt g (d v') v':= by
       have hs:= (sqrt_deriv hf (show 0<v'+v from add_pos hi.1 hv)).scomp (h:=fun x=>x+v) v' ((hasDerivAt_id' v').add (hasDerivAt_const v' v)); simp only [add_zero,one_smul] at hs; exact hs
   have hK : H^2<L+v:= by unfold L; linarith
   have hs := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f:=d) (μ:=volume) measurableSet_Ioi (Ioc_subset_Ioi_self (a:=L) (b:=(0:ℝ))) (fun w hw=> sqrt_above hf.raising (hK.trans <| add_lt_add_left (lt_of_not_ge fun q=>hw.2 ⟨hw.1,q⟩) v))
   change _*(∫ u in Ioi 0,d u)=_; rw [hs,← intervalIntegral.integral_of_le hL,intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL hg.continuousOn ht (he.intervalIntegrable ..)]
   simp only [g,sqrt_above hf hK,zero_add,zero_sub,mul_neg,neg_mul]
omit hH in
lemma patch_end {x : Plane} {z : ℂ} (hx:H < ‖x‖) : radial (fun s=> F (x,s)) z=0 := by
    have heq : (fun s=>F (x,s))=0:= by
       funext s; rw [he]; exact sqrt_above hf (by nlinarith only [hx,hf.size,norm_nonneg x,sq_nonneg s])
    rw [heq,emit_zero]
lemma descending (z : ℂ) : (∫ x : Plane, radial (fun t=> F (x,t)) (z-1))= radial f z:=by
   let X:= closedBall (0:Plane) H; let V:= H^2; let ν:= volume.restrict X; let J:= Icc 0 V; have hV :0≤V:=sq_nonneg _
   have hZ(z:ℂ) : (∫ x in X,radial (fun t=>F (x,t)) (z-1))= radial f z:= by
      refine congr_fun (wide (f:=fun z=>∫ x in X,radial (fun t=>F (x,t)) (z-1)) (drop_analytic hH hF (by unfold X; apply isCompact_closedBall) _ (differentiable_id.sub_const _)) (analytic hf) 1 ?_) z
      intro s hs; let r (v:Plane) (t:ℝ):= raised (fun t=>F (v,t)) t; let c:ℂ:= (↑π:ℂ)^s*(Gamma s)⁻¹; let w(t:ℝ):=(↑t:ℂ)^(s-1); let d:ℂ:=-(↑π)⁻¹
      have h' : 0<s.re:=zero_lt_one.trans hs
      have hv (t:Plane): radial (fun u=> F (t,u)) (s-1) = (d*c)*(∫ u in J,w u*r t (Real.sqrt u)):=by
         rw [radial_raised (hF t),sub_add_cancel,actual (hF t).raising h',support_mellin (hF t).raising (U:=V) le_rfl]
         unfold c d J w; rw [intervalIntegral.integral_of_le hV,integral_Icc_eq_integral_Ioc]; unfold r; ring
      -- Integrate both and exchange
      change ∫ x in X,radial (fun t=> F (x,t)) (s-1)=radial f s; simp_rw [hv]; rw [integral_const_mul,integral_integral_swap]
      · let φ (u:ℝ) := ∫ t in X,w u*r t (Real.sqrt u)
        have heq(u:ℝ) (hu:0<u): φ u = -(↑π:ℂ)*(w u*f (Real.sqrt u)) := by
           unfold φ r; rw [integral_const_mul]; simp_rw [raised_both hf hF he hu]; rw [setIntegral_eq_integral_of_forall_compl_eq_zero,eat_s hf hu]; ring
           intro a ha; have he:H<‖a‖:= lt_of_not_ge (fun h=> ha (mem_closedBall_zero_iff.mpr h)); apply sqrt_above hf.raising; nlinarith only [norm_nonneg a,hu,hf.size,he]
        have hk : (∫ u in J,φ u)= -(↑π:ℂ)*(rootM f s):= by
           rw [support_mellin hf (U:=V) le_rfl,intervalIntegral.integral_of_le hV,← integral_const_mul]; unfold J; rw [integral_Icc_eq_integral_Ioc]; exact setIntegral_congr_fun measurableSet_Ioc (fun t ht=>heq t ht.1)
        change _*(∫ u in J,φ u)=_; rw [hk,actual hf h']; unfold c d; have hP : (↑π:ℂ)≠0:= by exact_mod_cast Real.pi_ne_zero
        field_simp
      -- integrability compact
      unfold X J; rw [Measure.prod_restrict]; let P (v: Plane × ℝ):=w v.2*r v.1 (Real.sqrt v.2)
      refine ContinuousOn.integrableOn_compact (f:=P)  (IsCompact.prod (isCompact_closedBall ..) isCompact_Icc) (Continuous.continuousOn ?_)
      have hh : 0<(s-1).re:=by simpa
      exact ((continuous_ofReal_cpow_const hh).comp continuous_snd).mul ((raised_joint hH.1).continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)))
   rw [← hZ]; symm; exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=> patch_end hf hF he (lt_of_not_ge fun h=> hx (mem_closedBall_zero_iff.mpr h)))
end
end YM.MSbar.Dim
