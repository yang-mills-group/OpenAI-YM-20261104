import YM.SchemeRG11.Long.Mast
/-! Compact radial mark-aligned cost cut. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open scoped Classical ContDiff
variable {G:Gauge} {T:Align.Itinerary}
abbrev Window := ContDiffBump (0:E4)
variable (T)
def cove(B:Window):Slate:=fun i x=> B (incVec (T.gap i) x)
def barkS(B:Window)(k:Axis):Slate:=fun i x=>cove T B i (x-step k)-cove T B i x
lemma choice (B:Window):Plain T 0 (cove T B):=by
 refine ⟨⟨1,zero_lt_one,Eventually.of_forall (fun i p _=>?_)⟩,fun x _ _ z h=>?_⟩
 · rw [cove,zpow_zero,zpow_zero,mul_one,mul_one,abs_of_nonneg (ContDiffBump.nonneg ..)]; exact B.le_one
 refine ⟨B x,?_⟩; simp_rw [zpow_zero,one_mul]; exact B.continuous.continuousAt.tendsto.comp (show Tendsto _ atTop _ from h)
lemma inc_sum (a:ℝ)(x y:Cover):incVec a (x+y)=incVec a x+incVec a y:=by ext i; simp [Full.incVec,mul_add]
lemma inc_step(a:ℝ)(x:Cover)(k:Axis): incVec a (x-step k)-incVec a x= (-a) • basis k:=by ext i; simp [Full.incVec,mul_sub]
lemma secant (B:Window){p:E4}{z:ℕ → Cover}(h:Along T z p)(a:Axis) : Tendsto (fun i=> T.gap i^(-1:ℤ)*barkS T B a i (z i)) atTop (𝓝 (-(fderiv ℝ (⇑B) p (basis a)))):=by
 let x(i:ℕ):= incVec (T.gap i) (z i-step a); let y(i:ℕ):= incVec (T.gap i) (z i); let D:=fderiv ℝ (⇑B) p
 let f(i:ℕ):=B (x i)-B (y i)
 have he(i:ℕ):x i-y i=(-T.gap i) • basis a:=inc_step ..
 have hx:Tendsto x atTop (𝓝 p):=by simpa only [x,sub_eq_add_neg,Along] using h.shift (-step a)
 have hh := (((ContDiffBump.contDiff (n:=1) B).hasStrictFDerivAt (by decide) (x:=p)).isLittleO.comp_tendsto (hx.prodMk_nhds h)) -- check
 have hp:(fun i=> f i - D (x i-y i))=o[atTop] T.gap:= IsLittleO.trans_isBigO hh (show (fun i=> x i - y i)=O[atTop] T.gap from IsBigO.of_bound ‖basis a‖ (Eventually.of_forall (fun i=>by rw [he,norm_smul, norm_neg]; exact (mul_comm ..).le)))
 have hf:=hp.tendsto_div_nhds_zero.sub_const (D (basis a)); rw [zero_sub] at hf
 apply hf.congr; intro i; change (f i-_)/_ - _= _; rw [he,D.map_smul,smul_eq_mul,barkS,cove,cove,zpow_neg,zpow_one]; unfold f x y; have :=T.positive i; field_simp; ring
lemma estimate_Θ{B:Window}(a:Axis): ∃ A>0,∀ i x, |barkS T B a i x| ≤ A*T.gap i:=by
 let V:= fderiv ℝ (⇑B); have hp:IsCompact (tsupport V):=B.hasCompactSupport.fderiv ℝ; obtain ⟨C,hC⟩:= hp.exists_bound_of_continuousOn ((B.contDiff (n:=1)).continuous_fderiv (by simp)).continuousOn
 let e:= |C| +1
 have he(x:E4): ‖V x‖≤e:=by
   by_cases h:x∈tsupport V; · exact (hC x h).trans ((le_abs_self _).trans (by unfold e; linarith))
   rw [image_eq_zero_of_notMem_tsupport h,norm_zero]; unfold e; positivity
 refine ⟨e*(‖basis a‖+1),by unfold e; positivity,?_⟩; intro i x
 let y:=incVec (T.gap i) x; let z:=incVec (T.gap i) (x-step a)
 have hh:= (convex_univ (𝕜:=ℝ) (E:=E4)).norm_image_sub_le_of_norm_fderiv_le (x:=y) (y:=z) (f:=B) (fun x _=>B.contDiff (n:=1) |>.differentiable (by simp) |>.differentiableAt) (fun x _=> he x) trivial trivial -- check args
 refine le_trans hh ?_; rw [inc_step, norm_smul,norm_neg,Real.norm_of_nonneg (T.positive _).le]; calc _=(e*‖basis a‖)*T.gap i:=by ring
                                                                                             _ ≤ _:=by unfold e; have := T.positive i; gcongr; linarith
variable {T}
lemma allowNear (x:Cover)(i:ℕ): baseU T i x≤ ‖incVec (T.gap i) x‖+T.gap i:=by
 rw [norm_span _ (T.positive i),baseU,d,mul_add,mul_one]; gcongr
 · exact (T.positive i).le
 apply chart_ge
variable (T)
lemma envelop (B: Window)(a:Axis):∃ C>0, ∀ᶠ i in atTop,∀ x,barkS T B a i x≠0→ Near T C i x:=by
 -- from shifts distance
 let S:= |B.rOut| + ‖basis a‖ +2 -- unicode pipe issue
 refine ⟨S,by unfold S; positivity, ?_⟩
 filter_upwards [T.cutoff.eventually (ge_mem_nhds zero_lt_one)] with i hi x h
 apply le_trans (allowNear x i)
 let u:=incVec (T.gap i) (x-step a); let p:= incVec (T.gap i) x
 have hv: ‖p‖≤ ‖u‖+T.gap i * ‖basis a‖:=by have hh:=norm_sub_norm_le p u; rw [norm_sub_rev,inc_step,norm_smul,norm_neg, Real.norm_of_nonneg (T.positive _).le] at hh; linarith only [hh]
 change ‖p‖+_ ≤ _; have hb : ‖u‖< B.rOut ∨ ‖p‖< B.rOut:=by contrapose! h; change B u-B p=0; rw [B.zero_of_le_dist (by rw [dist_zero_right]; exact h.1),B.zero_of_le_dist (by rw [dist_zero_right]; exact h.2),sub_self]
 rcases hb with hb|hb <;> dsimp [S] <;> nlinarith [le_abs_self B.rOut,norm_nonneg (basis a)]
lemma biker (B: Window)(a:Axis): Plain T (-1) (barkS T B a):=by
 obtain ⟨C,hC,H⟩:= envelop T B a; obtain ⟨L,hL,h⟩:= estimate_Θ T (B:=B) a; refine ⟨⟨L*C,by positivity,H.mono ?_⟩,fun x h _ p hp=>⟨_,secant T B hp a⟩⟩
 intro i hi x _; by_cases ho:barkS T B a i x=0
 · rw [ho,abs_zero]; have := d_pos x; have := T.positive i; positivity
 refine (h i x).trans ?_; have he:d x>0:= d_pos _
 rw [zpow_zero,zpow_neg,zpow_one,mul_one]; apply (le_div_iff₀ he).mpr; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hi x ho) hL.le
end YM.SchemeRG11.Long
