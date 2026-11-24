import YM.SchemeConversionRG11.FirstMS.Triad.Patches

/-! Remove IR tail with its true radial Mellin factor. Index orientation of V retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {x:Nodes} {R ρ:ℝ} (h:Box x R ρ)
variable (l:P→Stem)(j:P)(a:Axis)

-- t cutoff β; multiply by compact mask cap(t/(4ρ)); entire effective interval unchanged.
def wing (x:Nodes)(ρ:ℝ): ℂ×ℝ×Patch →ℂ:= fun q=> vert q.1*(cap (q.2.1/(4*ρ)):ℂ)*(lip (Q q.2.2):ℂ)*vines l j a (q.2.1 • x) Finset.univ q.1 (swell q.2.2)

include h

lemma clears (t:ℝ)(ht: |t|≤4*ρ)(v:Patch)(hv:1/4 ≤ Q v)(k:P): move ((t • x) k) (swell v)∈region:= by
    have hl:= mul_le_mul_of_nonneg_right ht (norm_nonneg (x k)); have hy:=h.chest k
    rcases eq_or_ne v.1 (t • x k) with he|he
    · have hp : ‖v.1‖<4/128:= by rw [he,norm_smul,Real.norm_eq_abs]; linarith only [hl,hy]
      change 1/4≤‖v.1‖^2+v.2^2 at hv; change 0 < ‖v.1 - ((t • x) k)‖^2+v.2^2
      nlinarith only [sq_nonneg (‖v.1- ((t • x) k)‖),hv,pow_lt_pow_left₀ hp (norm_nonneg _) (by decide : (2:ℕ) ≠0)]
    exact show 0 < ‖v.1- t • x k‖^2+v.2^2 from add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) _) (sq_nonneg _)

private lemma wing_depart (v:ℝ × Patch)(hp: ¬ v∈ closedBall (0:ℝ) (4*ρ) ×ˢ closedBall (0:Patch) 1)(z:ℂ): wing l j a x ρ (z,v)=0:=by
    have hh:= h.size
    rcases not_and_or.mp hp with he|he
    · have hv : |v.1|/(4*ρ)>1:= (lt_div_iff₀ (by positivity)).mpr (by
        have hk : 4*ρ < |v.1|:= lt_of_not_ge fun ht=> he (mem_closedBall_zero_iff.mpr ht); linarith)
      unfold wing cap; rw [edge.zero_of_le_dist,ofReal_zero,mul_zero,zero_mul,zero_mul]
      rw [dist_zero_right,Real.norm_eq_abs,abs_div, abs_of_pos (show 0 < 4*ρ by positivity)]; exact hv.le
    have hv:1<‖v.2‖:= lt_of_not_ge fun ht=> he (mem_closedBall_zero_iff.mpr ht)
    unfold wing; rw [lip_ends ((one_lt_pow₀ hv (by decide : (2:ℕ)≠0)).trans_le (q_square _)), ofReal_zero,mul_zero,zero_mul]

private lemma wing_cd (q:ℂ × ℝ × Patch)(hq:q.1∈neighborhood): ContDiffAt ℝ ∞ (wing l j a x ρ) q:= by
    let K:=closedBall (0:ℝ) (4*ρ) ×ˢ closedBall (0:Patch) 1; have hK : IsCompact K:= IsCompact.prod (isCompact_closedBall ..) (isCompact_closedBall ..)
    by_cases he : q.2 ∈ K
    swap
    · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
      filter_upwards [((hK.isClosed.preimage continuous_snd).isOpen_compl.mem_nhds (show q∈(Prod.snd⁻¹' K)ᶜ from he))] with p hp
      exact wing_depart h l j a _ hp _
    rcases le_or_gt (1/4) (Q q.2.2) with hm|hm
    · let Qk(k:P)(x':ℂ × ℝ × Patch) : E4 := x'.2.1 • x (l k).loc
      have hh (k:P): ContDiffAt ℝ ∞ (fun p : ℂ × ℝ × Patch=> kind l j a k p.1 (p.2.2.1-Qk k p) (p.2.2.2^2)) q:=
         ((off_kind l j a k).smooth _ hq _ (clears h q.2.1 (mem_closedBall_zero_iff.mp he.1) _ hm (l k).loc)).comp (f:=fun p:ℂ×ℝ×Patch=>(p.1,p.2.2.1-Qk k p,p.2.2.2^2)) q (by unfold Qk; fun_prop)
      have hg : ContDiffAt ℝ ∞ vert q.1:= ((vert_analytic.analyticAt _).restrictScalars).contDiffAt
      have hf : ContDiffAt ℝ ∞ (fun q:ℂ × ℝ × Patch=> (cap (q.2.1/(4*ρ)):ℂ)) q:= (ofRealCLM.contDiff.comp (cap_smooth.comp (((contDiff_fst.comp contDiff_snd)).div_const _))).contDiffAt
      have hu : ContDiffAt ℝ ∞ (fun q:ℂ × ℝ × Patch=> (lip (Q q.2.2):ℂ)) q:= (ofRealCLM.contDiff.comp (lip_smooth.comp (q_smooth.comp (contDiff_snd.comp contDiff_snd)))).contDiffAt
      exact ((((hg.comp q contDiffAt_fst).mul hf).mul hu).mul (contDiffAt_prod (t:=Finset.univ) fun i _=> hh i))
    apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [((q_smooth.continuous.comp (f:=fun p:ℂ × ℝ × Patch=> p.2.2) (by fun_prop)).continuousAt (x:=q)|>.tendsto).eventually (gt_mem_nhds hm)] with p hp
    unfold wing; rw [lip_flats (show |Q p.2.2|<1/4 by rw [abs_of_nonneg (q_nonneg _)]; exact hp), ofReal_zero,mul_zero,zero_mul]

private lemma wing_dz (p:ℝ×Patch){z:ℂ}(hz:z∈neighborhood):DifferentiableAt ℂ (fun z=>wing l j a x ρ (z,p)) z:=by
   let K:=closedBall (0:ℝ) (4*ρ) ×ˢ closedBall (0:Patch) 1
   by_cases he : p ∈ K
   swap
   · simp_rw [wing_depart h l j a p he]; exact differentiableAt_const _
   rcases le_or_gt (1/4) (Q p.2) with hm|hm
   · have hh(k:P):= clears h p.1 (mem_closedBall_zero_iff.mp he.1) p.2 hm k
     exact (((vert_analytic z).mul_const (cap (p.1/(4*ρ)):ℂ)).mul_const (lip (Q p.2):ℂ)).mul (vine_color l j a (x:=p.1 • x) (K:=Finset.univ) (p:=(z,swell p.2)) hz fun k _=> hh (l k).loc)
   simp only [wing,lip_flats (show |Q p.2|<1/4 by rw [abs_of_nonneg (q_nonneg _)]; exact hm),ofReal_zero,mul_zero,zero_mul]; exact differentiableAt_const _

lemma wing_window : Window neighborhood 1 (wing l j a x ρ) := by
   let K:=closedBall (0:ℝ) (4*ρ) ×ˢ closedBall (0:Patch) 1; have hK : IsCompact K:= IsCompact.prod (isCompact_closedBall ..) (isCompact_closedBall ..)
   constructor
   · exact upon_packed opened hK (fun z hz t ht=> wing_depart h l j a t ht z) (wing_cd h l j a) (fun z p hz=> wing_dz h l j a p hz)
   · norm_num
   · intro z hz t v r; change wing _ _ _ _ _ (z,t,v,-r)=_; simp only [wing,Q,swell,neg_sq]
   intro z hz t v hv
   apply wing_depart h l j a (t,v)
   exact fun he => not_le.mpr hv (mem_closedBall_zero_iff.mp he.2)

def high (x:Nodes)(ρ:ℝ) (z:ℂ) := ∫ t in Ioc 0 ρ,(t:ℂ)^(5+4*z)*billAt z (fun v => wing l j a x ρ (z,t,v))
lemma high_analytic {z:ℂ}(hz:z∈neighborhood) : AnalyticAt ℂ (high l j a x ρ) z:= by
   refine (weight_ok opened h.size.le (q:=fun z=> 5+4*z) (fun z hz=> by fun_prop) ?_ ((wing_window h l j a).integral opened)).analytic opened hz 0
   intro z hz; have hx : ‖z‖<1/8:= by simpa [neighborhood] using hz
   have he:=abs_re_le_norm z
   rw [abs_le] at he; simp; linarith [he.1,he.2]

lemma wing_moving (p:Patch){t:ℝ}(ht : t ∈ Ioc 0 ρ)(hz:1/4 ≤ Q p){s:ℂ}(hs : s∈neighborhood) :
    vines l j a x Finset.univ s (swell (t⁻¹ • p)) = ((↑t⁻¹:ℂ)^(-10-6*s))*vines l j a (t • x) Finset.univ s (swell p) := by
    have hp : 0<t:=ht.1; have hu:0<t⁻¹:=by positivity
    let D:= fun j:P=>move ((t • x) j) (swell p)
    have hh {k:P} (j:P): (move (x j) (swell (t⁻¹ • p))).1 = t⁻¹ • (D j).1:= by
       change t⁻¹ • p.1 - x j=t⁻¹ • (p.1 - t • x j); rw [smul_sub,inv_smul_smul₀ hp.ne']
    have hv(k:P): kind l j a k s (move (x (l k).loc) (swell (t⁻¹ • p))).1 (swell (t⁻¹ • p)).2 = (((t⁻¹:ℝ):ℂ)^(S j k s))*kind l j a k s (D (l k).loc).1 ((swell p).2):= by
       rw [hh (k:=k)]
       have hv : |t| ≤ 4*ρ:= by rw [abs_of_pos hp]; linarith [ht.2]
       have he := (owns_kind l j a k) _ hs _ (clears h _ hv p hz (l k).loc) t⁻¹ hu
       rw [show (swell (t⁻¹ • p)).2=t⁻¹^2*(D (l k).loc).2 by change (t⁻¹*p.2)^2=t⁻¹^2*p.2^2; ring]; exact he
    unfold vines; simp_rw [hv,Finset.prod_mul_distrib]
    congr 1
    rw [Fin.prod_univ_three]; simp_rw [← cpow_add _ _ (show (↑(t⁻¹):ℂ)≠0 by exact_mod_cast hu.ne')]
    fin_cases j <;> simp +decide only [S, ↓reduceIte] <;> ring_nf

theorem border :
    let f(v:E4) := (↑(1-last ρ (v,0)):ℂ) * vines l j a x Finset.univ 0 (v,0)
    Integrable f ∧ high l j a x ρ 0=∫ v,f v := by
   intro f
   let G(v:E4):= vines l j a x Finset.univ 0 (v,0)
   have hh:=wing_window h l j a
   let F(t:ℝ×E4):= (↑t.1:ℂ)^5*wing l j a x ρ (0,t.1,t.2,0)
   let K:=closedBall (0:ℝ) (4*ρ) ×ˢ closedBall (0:E4) 1
   have hf : IsCompact K:= IsCompact.prod (isCompact_closedBall ..) (isCompact_closedBall ..)
   have H : HasCompactSupport F:= by
      refine hf.of_isClosed_subset (isClosed_tsupport F) (closure_minimal (fun t ht=> ?_) hf.isClosed)
      by_contra hk; apply ht
      unfold F; rw [wing_depart h l j a _ _ 0, mul_zero]
      intro he; exact hk ⟨he.1,mem_closedBall_zero_iff.mpr ((norm_fst_le (t.2,(0:ℝ))).trans (mem_closedBall_zero_iff.mp he.2))⟩
   have he(t:ℝ)(v:E4)(ht:t∈ Ioc 0 ρ): F (t,v)= (t⁻¹)^5 • (lip (‖v‖^2) • G ((0:E4)+t⁻¹ • v)):=by
      have hu: Q (v,0)=‖v‖^2:= by simp [Q,total,swell]
      have hp:= ht.1; have hr:= h.size
      unfold F wing; rw [hu]
      by_cases hc : Q (v,0)<1/4
      · rw [lip_flats (show |‖v‖^2|<1/4 by rw [abs_of_nonneg (sq_nonneg _)]; rwa [hu] at hc)]; simp
      have hd := wing_moving h l j a (v,0) ht (le_of_not_gt hc) occurs
      simp only [mul_zero,sub_zero,cpow_neg, cpow_ofNat, ofReal_inv, inv_pow, inv_inv, swell,Prod.smul_snd, Prod.smul_fst, smul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hd
      have hb: cap (t/(4*ρ))=1 := cap_flat (by rw [abs_of_nonneg (by positivity : 0 ≤ t/(4*ρ)),div_le_iff₀ (by positivity)];linarith [ht.2])
      have hk : (t:ℂ)≠0:=ofReal_ne_zero.mpr hp.ne'
      simp only [hb,ofReal_one,mul_one,vert,cpow_zero,one_mul,zero_add,G,hd,real_smul,ofReal_pow,ofReal_inv]
      unfold swell; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]; field_simp
   have hm : Measurable G := by
      unfold G vines; refine Finset.measurable_prod _ fun i _=>?_
      exact (off_measured (off_kind l j a i) occurs).comp (f:=fun v:E4=>v-x (l i).loc) (by fun_prop)
   have hC: Continuous F := ((continuous_ofReal.comp continuous_fst).pow 5).mul ((hh.AH'.slice occurs).1.continuous.comp (f:=fun t:ℝ×E4=> (t.1,t.2,(0:ℝ))) (by fun_prop))
   have hi:= outside_part (T:=curry F) (x:=0) h.size hm (fun t ht=> Eventually.of_forall fun v=> he t v ht) (hC.integrable_of_hasCompactSupport H)
   have hy (v:E4):(1-cap (‖v-(0:E4)‖^2*ρ^2)) • G v=f v:= by simp [f,G,last,total,real_smul]
   simp_rw [hy] at hi
   refine ⟨hi.1,(Eq.trans ?_ hi.2.symm)⟩
   apply integral_congr_ae (μ:=volume.restrict (Ioc 0 ρ)); refine Eventually.of_forall fun t=> ?_
   change (↑t:ℂ)^(5+(4:ℂ)*0)*_ = ∫ v:E4, F (t,v)
   rw [mul_zero,add_zero,cpow_ofNat,hh.zero t occurs]; exact (integral_const_mul (μ:=volume) ((↑t:ℂ)^ (5:ℕ)) (fun v:E4=> wing l j a x ρ (0,t,v,0))).symm

end YM.SchemeConversionRG11.FirstMS.Triad
