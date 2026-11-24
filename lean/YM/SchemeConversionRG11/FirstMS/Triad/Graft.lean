import YM.SchemeConversionRG11.FirstMS.Triad.Mixing

/-! Open two-hat evanescent CT and the subgraph after sewing. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

private theorem layer_monomial (c:ℂ)(n:ℕ): layer n (fun t:ℝ=>(t:ℂ)^n * c) 0=c := by
   induction n with
   | zero=> simp
   | succ n ih=>
     have he : strip (fun t:ℝ=> (t:ℂ)^(n+1)*c)=fun t:ℝ=> (t:ℂ)^n*c:= by
        ext1 t
        have hf : HasTemperateGrowth (fun t:ℝ=> (t:ℂ)^(n+1)*c):= by
           apply HasTemperateGrowth.mul (g:=fun _=>c) _ (HasTemperateGrowth.const c); clear ih; induction n with
           | zero=> simpa using! ofRealCLM.hasTemperateGrowth
           | succ n ih=> exact (by simp_rw [pow_succ (n:=n+1)]; exact ih.mul ofRealCLM.hasTemperateGrowth)
        rcases eq_or_ne t (0:ℝ) with rfl|hr
        · let f:=fun t:ℝ=> (t:ℂ)^n*c
          have hp : Continuous f:= (continuous_ofReal.pow n).mul_const c
          exact tendsto_nhds_unique_of_eventuallyEq ((strip_tame_ray hf).1.continuous.continuousWithinAt (x:=(0:ℝ)) (s:=Ioi 0)) (hp.continuousWithinAt) (mem_of_superset self_mem_nhdsWithin (fun x hx=> by
            have h:x≠0:= (Set.mem_Ioi.mp hx).ne'
            have hu: (↑x:ℂ)≠0:= by exact_mod_cast h; -- simp
            simp [strip,dslope_of_ne _ h,f,slope_def_module]; field_simp; ring))
        have hu: (↑t:ℂ)≠0:= by exact_mod_cast hr
        simp [strip,dslope_of_ne _ hr,slope_def_module]; field_simp; ring
     unfold layer; rw [iterate_succ_apply,he]; exact ih

-- q is one of finitely many physical monomials of degree n-2.
variable (F:ℂ→E4→ℝ→ℂ) (q:E4→ℂ)

def wheel (s:ℂ):= billAt s (fun p:Patch=> (↑(p.2^2):ℂ)*(vert s*shape F s p*q p.1))
def hub (s:ℂ):= dslope (wheel F q) 0 s/2

def hatCT : ℂ:= -(hub F q 0)/2

section Hat
variable {F q} (hF:Off F)(hq:HasTemperateGrowth q)
include hF hq

private lemma wheel_window :
    Window neighborhood 1 (fun x:ℂ×ℝ×Patch=>
      (↑(x.2.2.2^2):ℂ)*(vert x.1*shape F x.1 x.2.2*q x.2.2.1)) := by
    refine ⟨?_,by norm_num,(fun z _ t v r=> by simp only [neg_sq,shape_flip]), fun z _ x p hp=> by simp only [shape_ends F hp,mul_zero,zero_mul]⟩
    apply AH.mul (AH.param_tame (g:=fun x:ℝ × Patch=> (↑(x.2.2^2):ℂ)) (ofRealCLM.hasTemperateGrowth.comp (by fun_prop : HasTemperateGrowth (fun x:ℝ × Patch=> x.2.2^2))))
       (((AH.holomorphic opened (vert_analytic.differentiableOn)).mul ((shape_bill hF).arguments (w:=Prod.snd) tame_projR)).mul (AH.param_tame (hq.comp (by fun_prop : HasTemperateGrowth (fun x:ℝ × Patch=>x.2.1))))) -- mismatch

lemma wheel_analytic {s:ℂ}(hs:s∈neighborhood) : AnalyticAt ℂ (wheel F q) s := ((wheel_window hF hq).integral opened).analytic opened hs 0

lemma wheel_zero : wheel F q 0=0:=by
   have he := (wheel_window hF hq).zero 0 occurs
   unfold wheel; simpa using he

lemma hub_analytic {s:ℂ}(hs:s∈neighborhood) : AnalyticAt ℂ (hub F q) s:= by
   rcases eq_or_ne s 0 with rfl|hr
   · obtain ⟨p,hp⟩:= wheel_analytic hF hq occurs
     exact hp.has_fpower_series_dslope_fslope.analyticAt.div analyticAt_const (by norm_num)
   have hd : AnalyticAt ℂ (fun z=> (z⁻¹ * wheel F q z)/2) s := ((((analyticAt_id (𝕜:=ℂ)).inv hr).mul (wheel_analytic hF hq hs)).div analyticAt_const (by norm_num))
   apply hd.congr
   filter_upwards [eventually_ne_nhds hr] with t ht; simp [hub,dslope_of_ne _ ht, slope_def_module,wheel_zero hF hq]

omit hq in
private lemma ticket {s:ℂ}(hs:s∈neighborhood)(v:E4) (q:E4→ℂ): crown.Fiber 1 (fun r=>vert s*((↑(lip (‖v‖^2+r)):ℂ)*F s v r)*q v) := by
   refine ⟨by norm_num,fun r hr=>?_,fun r hr=>?_⟩
   · rcases eq_or_lt_of_le (show 0≤‖v‖^2+r from by positivity) with he|hp
     · refine (contDiffAt_const (x:=r) (c:=(0:ℂ))).congr_of_eventuallyEq ?_
       have hm : ∀ᶠ x : ℝ in 𝓝 r, |‖v‖^2+x| < 1/4 := by
          exact ((continuous_id'.const_add (‖v‖^2)).abs.continuousAt (x:=r)|>.tendsto).eventually (gt_mem_nhds (show |‖v‖^2+r|<1/4 by rw [←he]; norm_num))
       filter_upwards [hm] with x hx; simp only [lip_flats hx,ofReal_zero,zero_mul,mul_zero]
     have hh:= (hF.smooth _ hs (v,r) hp).comp (f:=fun t:ℝ=> (s,v,t)) r (by fun_prop)
     exact (contDiffAt_const.mul (((ofRealCLM.contDiff.comp (lip_smooth.comp (contDiff_const.add contDiff_id))).contDiffAt).mul hh)).mul contDiffAt_const
   simp only [lip_ends (p:=‖v‖^2+r) (by exact lt_of_lt_of_le (by simpa using hr : 1 < r) (le_add_of_nonneg_left (sq_nonneg _))), ofReal_zero,zero_mul,mul_zero]

/-- Actual projected hat moment in a one-auxiliary-plane work with an open-index test.
   Genuine analytic coefficient hub, not replacing hats by zero inside the UV pole. -/
lemma hub_draw (i:Dim.fin 1){s:ℂ}(hz:s≠0)(hs:s∈neighborhood) :
    hub F q s = ∫ v:E4,Dim.plate s (crown.frameLine (fun r=> vert s*((↑(lip (‖v‖^2+r)):ℂ)*F s v r)*q v) i) := by
    have he:= sub_smul_dslope (wheel F q) 0 s; rw [sub_zero, smul_eq_mul,wheel_zero hF hq,sub_zero] at he
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hz)
    rw [show 2*s*hub F q s=s*dslope (wheel F q) 0 s by unfold hub; ring, he,← integral_const_mul]; unfold wheel
    exact integral_congr_ae (Eventually.of_forall fun v=> (crown.canonical_hat (ticket hF hs v q) s i).symm)

lemma taylor_hat (n:ℕ){R:ℝ}(hr:0<R):
    let w(p:ℂ×ℝ):= (p.2:ℂ)^n * hub F q p.1
    Unfolds (due n w R) (hatCT F q) := by
   intro w
   have hp : HasTemperateGrowth (fun t:ℝ=>(t:ℂ)^n):=by
      induction n with
      | zero=> simpa only [pow_zero] using HasTemperateGrowth.const (E:=ℝ) (F:=ℂ) 1
      | succ i ih=> simp_rw [pow_succ]; exact ih.mul ofRealCLM.hasTemperateGrowth
   have he : AH neighborhood w:= (AH.param_tame hp).mul (AH.holomorphic opened (fun z hz=> (hub_analytic hF hq hz).differentiableAt.differentiableWithinAt))
   unfold hatCT; rw [←layer_monomial (hub F q 0) n]; exact due_open he hr n
end Hat

-- ext(q,z) linear in physical β slots supplying hat² CT through degree3
variable {F q} {R:ℝ}{T:sheet}

def component (i: Axis) (x:E4):ℂ:= ↑(x i)

def extra (F:ℂ→E4→ℝ→ℂ) (T:sheet) (added:Bool)(z:ℂ):=
   if !added then slit T (z,0)*hatCT F (fun _=>1)
   else ∑ i:Axis, ladd (fun v=> slit T (z,v)) 1 (basis i) *hatCT F (component i)

def thickness (added:Bool):ℕ := if !added then 2 else 3

lemma extra_analytic (hT:Touch R T)(added:Bool){z:ℂ}(hz:z∈neighborhood) : AnalyticAt ℂ (extra F T added) z := by
   cases added
   · exact ((hT.spare.analytic opened hz 0).mul (analyticAt_const (v:=_)))
   exact Finset.analyticAt_fun_sum Finset.univ (fun i _=> (((analytic_ray hT.spare 1).analytic opened hz (basis i)).mul (analyticAt_const (v:=hatCT F (component i)))))

lemma extra_linear (hT:Touch R T) {z:ℂ}(hz:z∈neighborhood)(v:E4) :
    ladd (fun v=> slit T (z,v)) 1 v = ∑ i:Axis,component i v *ladd (fun v=>slit T (z,v)) 1 (basis i) := by
   let L:= fderiv ℝ (fun v=>slit T (z,v)) 0
   have he(x:E4):ladd (fun v=> slit T (z,v)) 1 x=L x:= by
      simp only [ladd,layer,Function.iterate_one,strip,dslope_same]
      have hv : HasDerivAt (fun r:ℝ=> r • x) x 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
      have hh:= ((hT.spare.slice hz).1.differentiable (by simp) 0).hasFDerivAt
      exact ((show HasFDerivAt (fun v=>slit T (z,v)) L ((0:ℝ) • x) by simpa using hh).comp_hasDerivAt 0 hv).deriv
   simp_rw [he,component,← Complex.real_smul,← map_smul,← map_sum]
   congr
   simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using ((EuclideanSpace.basisFun Axis ℝ).sum_repr v).symm

-- ren pair to b, applied to T_z radial ext

def pair (F:ℂ→E4→ℝ→ℂ)(T:sheet)(R:ℝ)(added:Bool)(z:ℂ) :=
    due (thickness added) (fun p=> billAt p.1 (fun v=> servo F T (p.1,p.2,v))) (4*R) z -
       z⁻¹ * (phys F (thickness added) (centry T z) + 2*z * extra F T added z)

lemma pair_fin (hF:Off F)(hT:Touch R T)(added:Bool) : ∃ g:ℂ→ℂ, AnalyticAt ℂ g 0 ∧ pair F T R added =ᶠ[walks] g:= by
   let f(z:ℂ):= phys F (thickness added) (centry T z)
   obtain ⟨g,hg,ht⟩:= entry_pole hF hT (thickness added)
   obtain ⟨p,hp⟩:= entry_deriv hF hT (thickness added) occurs
   refine ⟨fun z=> g z-dslope f 0 z -2*extra F T added z,(hg.sub hp.has_fpower_series_dslope_fslope.analyticAt).sub (analyticAt_const.mul (extra_analytic hT added occurs)),?_⟩
   filter_upwards [ht,self_mem_nhdsWithin] with z hz he
   have hw : z≠0:=he
   unfold pair; rw [hz]
   change z⁻¹*f 0+_-(z⁻¹*(f z+_))=_
   rw [dslope_of_ne _ hw,slope_def_module]; simp only [sub_zero,smul_eq_mul]
   field_simp; ring

end YM.SchemeConversionRG11.FirstMS.Triad
