import YM.PertExtension.Interior
import YM.PertExtension.Aspiration
/-! Generic fixed-dimensional radial approximation on arbitrary finite patches. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Sway.Local
open Function Filter Set MeasureTheory Metric PertExtension.Series Radial Tested
open scoped Classical ContDiff Topology BigOperators
variable {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]

def Goal(f:E→ℝ):Prop:= ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u
lemma regrows {f g:E→ℝ}(h:f=ᶠ[𝓝 0]g): jet f=jet g:=by
 funext n u; unfold jet; rw [(h.iteratedFDeriv ℝ _).eq_of_nhds]
lemma seed_eq{f g:E→ℝ}(h:Stationary f)(hf:g=ᶠ[𝓝 0]f):Stationary g:= ⟨h.smooth.congr_of_eventuallyEq hf,hf.eq_of_nhds.trans h.base0,fun u=>by rw [regrows hf,h.base1]⟩
lemma scion_eq{f g K J:E→ℝ}(hf:f=ᶠ[𝓝 0]g)(hK:K=ᶠ[𝓝 0]J): normTerm K f=normTerm J g:=by
 funext i x; unfold normTerm integrandSeries layers Radial.kernel; rw [regrows hK, regrows hf]
variable [FiniteDimensional ℝ E]
lemma damp{f:E→ℝ}(hf:Stationary f)(g:Goal f): ∃ c>0, ∀ᶠ x in 𝓝 0, c*‖x‖^2≤f x:= by
 obtain ⟨C,hC,hf'⟩:=g
 obtain ⟨δ,M,hδ,hM,h⟩:=hf.dominated (half_pos hC)
 refine ⟨C/2, half_pos hC,?_⟩
 filter_upwards [closedBall_mem_nhds (0:E) hδ] with x hx
 have he: ‖higher f 1 x‖≤C/2*‖x‖^2:= (h x 1 one_pos (by simpa using hx)).2
 unfold higher at he; simp only [one_pow,one_smul,div_one,Real.norm_eq_abs, abs_le] at he
 linarith [hf' x]
lemma parler{c:ℝ}(hc:0<c)(n:ℕ): ∃ C,0≤C ∧ ∀ t:ℝ,0<t → Real.exp (-c/t^2) ≤ C*t^n:=by
 obtain ⟨C,hC,h⟩:=bounded_exp hc n
 refine ⟨C,hC,fun t ht=>?_⟩
 apply le_of_mul_le_mul_left (a:=t⁻¹^n) ?_ (by positivity)
 rw [show t⁻¹^n*(C*t^n)=C from by rw [mul_left_comm,inv_pow, inv_mul_cancel₀ (by positivity),mul_one]]
 convert le_trans ?_ (h t⁻¹ (by positivity)) using 1
 rw [inv_pow t 2,← div_eq_mul_inv]; gcongr; linarith

variable [MeasurableSpace E] [BorelSpace E] (μ: Measure E)[μ.IsAddHaarMeasure]
def aurum(K f:E→ℝ)(S:Set E)(t:ℝ):= (t^Module.finrank ℝ E)⁻¹ *(∫ x in S,K x*Real.exp (-f x/t^2) ∂μ)
lemma aurum_ball (K f:E→ℝ)(r:ℝ){t:ℝ}(ht:0≤t): aurum μ K f (ball 0 r) t=partialSum μ K f r t:=by
 let S:= ball (0:E) r; let T:= disc (E:=E) t r
 let g(x:E):= K x*Real.exp (-f x/t^2)
 have hh(x:E): S.indicator g (t • x)=T.indicator (projection K f t) x:=by
    by_cases hx: t • x∈ S
    · rw [indicator_of_mem hx,indicator_of_mem (s:=T) hx]; exact (projection_eq ..).symm
    rw [indicator_of_notMem hx,indicator_of_notMem (s:=T) hx]
 have hu:= Measure.integral_comp_smul_of_nonneg μ (S.indicator g) t (hR:=ht)
 simp_rw [hh] at hu; rw [integral_indicator isOpen_ball.measurableSet,integral_indicator (disc_meas ..)] at hu
 exact hu.symm
omit [FiniteDimensional ℝ E] in
lemma aurum_cut{K f:E→ℝ}{s b:Set E}{c:ℝ}(hc:0<c)(g: ∀ x∈s\b,c≤f x)(hs: IsCompact s)(hb: MeasurableSet b)(h:b⊆s)(hK:ContinuousOn K s)(hf:ContinuousOn f s)(n:ℕ): Bill n (aurum μ K f s-aurum μ K f b):=by
 let N:= Module.finrank ℝ E; let T:=s\b
 obtain ⟨D,hD,hd⟩:= parler hc (n+N)
 obtain ⟨M,hM⟩:= hs.exists_bound_of_continuousOn hK
 let C:= |M| * D * μ.real T
 refine ⟨C,by unfold C; positivity,?_⟩
 filter_upwards [Tested.eventually_pos] with t ht
 let F(x):= K x*Real.exp (-f x/t^2)
 have hi: IntegrableOn F s μ:= (ContinuousOn.integrableOn_compact hs (f:=F) (hK.mul (Real.continuous_exp.comp_continuousOn (hf.neg.div_const (t^2)))))
 have he: (aurum μ K f s-aurum μ K f b) t=(t^N)⁻¹* (∫ x in T,F x ∂μ):=by
    rw [setIntegral_sdiff hb hi h,mul_sub]; rfl
 rw [he,norm_mul,Real.norm_eq_abs ((t^N)⁻¹),abs_of_nonneg (by positivity)]
 calc
    _ ≤ (t^N)⁻¹ * (|M| * (D*t^(n+N)) * μ.real T):=by
       gcongr
       refine norm_setIntegral_le_of_norm_le_const (lt_of_le_of_lt (measure_mono sdiff_subset) hs.measure_lt_top) (fun x hx=>?_)
       unfold F; rw [norm_mul, Real.norm_eq_abs (Real.exp ..),abs_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul ((hM x hx.1).trans (le_abs_self _)) ((Real.exp_le_exp.mpr ?_).trans (hd t ht)) (Real.exp_pos _).le (abs_nonneg _)
       gcongr; exact g x hx
    _=C*t^n:=by unfold C; rw [pow_add]; field_simp
lemma aurum_gain {K f:E→ℝ}(hK: ContDiffAt ℝ ∞ K 0)(hf:Stationary f)(g:Goal f): ∃ U∈𝓝 (0:E), ∀ S:Set E,S⊆U → S ∈ 𝓝 0 → IsCompact S → Aspiration (aurum μ K f S) (Radial.moment μ K f):=by
 obtain ⟨c,hc,h⟩:= damp hf g
 let U:= {x:E | c*‖x‖^2≤f x ∧ ContinuousAt K x ∧ ContinuousAt f x}
 have hU : U ∈ 𝓝 0:= h.and <| by
   refine (?_: ∀ᶠ x in 𝓝 0, ContinuousAt K x).and ?_
   · exact ((hK.of_le (by exact show (0:WithTop ℕ∞) ≤ ∞ from bot_le)).eventually (by simp)).mono fun i hi=>hi.continuousAt
   exact ((hf.smooth.of_le (by exact show (0:WithTop ℕ∞)≤∞ from bot_le)).eventually (by simp)).mono fun i hi=>hi.continuousAt
 refine ⟨U,hU,fun S hs hn hm n=>?_⟩
 have hv:ContinuousOn f S:=fun x hx=> (show ContinuousAt f x from (hs hx).2.2).continuousWithinAt
 have hl:ContinuousOn K S:=fun x hx=> (show ContinuousAt K x from (hs hx).2.1).continuousWithinAt
 let F:=S.indicator f; let H:=S.indicator K
 have he: F=ᶠ[𝓝 0] f:=Filter.Eventually.mono (p:=fun x=>x∈S) hn (fun x hx=>indicator_of_mem hx _)
 have he': H=ᶠ[𝓝 0] K:=Filter.Eventually.mono (p:=fun x=>x∈S) hn (fun x hx=>indicator_of_mem hx _)
 obtain ⟨δ,hδ,hd⟩:= Stationary.rescale_estimate (μ:=μ) (F:=seed_eq hf he) (K:=H) (hf:=hK.congr_of_eventuallyEq he') (hl.measurable_piecewise continuousOn_const hm.measurableSet) (hv.measurable_piecewise continuousOn_const hm.measurableSet) (by rw [regrows he]; exact g) n
 obtain ⟨d,hd',hD⟩:= Metric.mem_nhds_iff.mp hn
 let r := min d (δ/2)
 have hr:0<r:=lt_min hd' (half_pos hδ); let T:= ball (0:E) r
 have hT:T⊆S:=Set.Subset.trans (ball_subset_ball (min_le_left ..)) hD
 obtain ⟨C,hC⟩:= hd r ⟨hr,(min_le_right ..).trans_lt (half_lt_self hδ)⟩
 have ht:Bill (n+1) (aurum μ K f T - peval (Radial.moment μ K f) n):=by
    refine ⟨|C|,abs_nonneg _,?_⟩
    filter_upwards [hC,Tested.eventually_pos] with t ht ht'
    have hv: aurum μ K f T t=partialSum μ H F r t:=by
       rw [← aurum_ball μ _ _ r ht'.le]; unfold aurum; congr 1; refine setIntegral_congr_fun isOpen_ball.measurableSet fun x hx=>?_ ; rw [show F x= f x from indicator_of_mem (hT hx) _, show H x= K x from indicator_of_mem (hT hx) _]
    have hg:Radial.moment μ H F= Radial.moment μ K f:=by unfold Radial.moment; rw [scion_eq he he']
    rw [←hg, Pi.sub_apply,hv]; change ‖partialSum .. - peval (Radial.moment μ H F) n t‖≤ _; refine le_trans ?_ (show C*t^(n+1) ≤ |C| * t^(n+1) by gcongr; apply le_abs_self); simpa only [peval,Zone.eval,smul_eq_mul] using ht
 have hw:∀ x∈ S\T,c*r^2≤ f x:=fun x hx=> le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (show r ≤ ‖x‖ by simpa [T] using hx.2) _) hc.le) (show c*‖x‖^2 ≤ f x from (hs hx.1).1)
 have hb:=aurum_cut μ (by positivity:0<c*r^2) hw hm isOpen_ball.measurableSet hT hl hv (n+1)
 simpa only [sub_add_sub_cancel] using bill_add hb ht
end YM.SchemeRG11.Sway.Local
