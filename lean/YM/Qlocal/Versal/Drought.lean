import YM.Qlocal.Quipu.Tax
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Calculus
/-!
# The real momentum read
 All periods. Actual flag mask required for prices. Calendar purchase later, but non-varying-parameter price geometry given. Support includes all root and emitted curvature paths; query can keep even more points. Theta model (group-output kernel, including `tan=true` optional) is REAL and does not bake in any local chart or log. Estimate path winding lengths and exposures before projection/coupling. Keep θ threshold normalization (not crude positive estimate off mask).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Vase
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
variable (l:Lattice.Order){s:Senses R}(A:Vase s G n)(x:Site c)(W:Config G c)(o:Site c)(p:BudgetPoint)
set_option quotPrecheck false
-- location estimates at covers.On-pre support exponent.
local notation "Ξ" => A.momentum
lemma walks_first (y:Site c)(w:Walk) (hi:y∈ Crown w o) : separation o y ≤ w.length := by
 rw [found_crown,List.mem_toFinset] at hi; induction w generalizing o with
 | nil=> simp only [visits,List.mem_singleton] at hi; simp [hi]
 | cons a l ih=> rcases List.mem_cons.mp hi with h|h; simp [h]; have hx:=separation_triangle o (o+a.vec) y; have hm:= ih (o+a.vec) h; have hv : separation o (o+a.vec) ≤ 1:=UVNext.PricedKernels.oneStep_le o a; simp only [List.length_cons]; omega
lemma birthplace : x∈ A.cone l x := by unfold cone coin; refine mem_image.mpr ⟨0,mem_union_left _ (mem_insert_self ..),?_⟩; rw [Lasso.bent,map_zero,zero_add]
lemma radius (y:Site c)(hi:y∈A.cone l x): separation x y ≤ A.momentum := by
 obtain ⟨c,hc,rfl⟩:= mem_image.mp hi; rcases mem_union.mp hc with h|h
 · rcases mem_insert.mp h with rfl|h; · simp [Lasso.bent]
   obtain ⟨i,hi,hh⟩:= mem_biUnion.mp h; let w:=route 0 (A.stage.pursue i) l; have hh' : separation x (bent x c)≤ w.length:= walks_first x _ w (mem_image_of_mem _ hh)
   rw [show w.length=size (A.stage.pursue i) by unfold w; rw [route_length,sub_zero]] at hh'; exact hh'.trans ((A.stage.stable _ hi).trans (Nat.le_add_left ..))
 obtain ⟨i,hi,hh⟩:=mem_biUnion.mp h; let w:= (A.maps i).tour; exact (walks_first x _ w (mem_image_of_mem _ hh)).trans ((Nat.le_add_left ..).trans (A.covered i))
-- Brush amends with valuation at every Theta stamp
noncomputable def bloom (G:Gauge) (r:ℕ): ℝ := 1+(theta_held G r).choose
lemma springGe (G:Gauge)(r:ℕ): 1≤ bloom G r:= le_add_of_nonneg_right (theta_held G r).choose_spec.1
lemma value_t {W0:G.El} (hw:‖G.curvature W0‖≤1) (hr:G.chord W0≤a) (q:Bool): ‖amend G k q W0‖ ≤ bloom G k *a := by
   unfold amend; split_ifs with h -- may need unfold below
   · exact ((theta_held G k).choose_spec.2 _ (hw.trans (by norm_num))).trans (mul_le_mul (le_add_of_nonneg_left zero_le_one) ((G.curvature_norm W0).trans hr) (norm_nonneg _) (zero_le_one.trans (springGe ..)))
   exact ((G.curvature_norm _).trans hr).trans (le_mul_of_one_le_left ((norm_nonneg _).trans ((G.curvature_norm _).trans hr)) (springGe ..))
variable (r:ℕ) {d t:ℝ}
noncomputable def cloud (G:Gauge)(k r:ℕ)(d:ℝ)(n:ℕ):= bloom G r*n + (1 + velocity G n d)^k * rate G k r
lemma fog (G:Gauge)(k r:ℕ) (u:ℕ) (hd:0≤d):0≤cloud G k r d u:= by
 unfold cloud velocity; have hx:= springGe G r; have hp:= royalty_ge G; have ht:=rated G k r; positivity
private lemma seep (G:Gauge)(n:ℕ)(d t:ℝ): velocity G n (t*d)=velocity G n d*t:=by unfold velocity; ring
local notation "π"=> A.cone l x
local notation "C!"=> cloud G k r d A.momentum
section smooth
variable [NormedAddCommGroup E][NormedSpace ℝ E]{y:E}{U:E→ Config G c}
    {d t:ℝ} (hd:0≤d) (ht:0≤t) (hk:t≤1) (hv:Healthy t (A.cone l x) (U y)) (hU:Mode U y k (t*d))
-- (positive grades in derivatives) ×t^n even if W.chart orientation relative unknown. Sustain directions 
include hd ht hk hv hU
local notation "τ"=> t*d
lemma breath (i:Fin n) : Brush k (cloud G k r d A.momentum*t) 1 (fun z=> amend G r (A.tan i) (travel (U z) x (A.maps i).tour)) y := by
 let w:ℝ:=velocity G A.momentum d; let μ:= (A.maps i).tour; have hm:= amended A x hU i r; rw [seep] at hm; have hx : 0≤ w:= by unfold w velocity; have hr:= royalty_ge G; positivity
 refine ⟨hm.smooth,zero_le_one,?_⟩; rintro (_|q) hlq
 · unfold normJ; rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]; have h := sculpt (g:=fun z=> travel (U z) x (A.maps i).tour) (tour (A.maps i).tour x hU.pos hU.atLink)
   have hX : G.chord (travel (U y) x μ) ≤ t*A.momentum:= ((A.maps i).ballot _ x ht (disjoint_of_subset_left (A.belongs l x i) hv)).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show (A.maps i).range≤ A.momentum from (Nat.le_add_right ..).trans (A.covered i))) ht)
   have hU' : bloom G r*A.momentum ≤ cloud G k r d A.momentum:=le_add_of_nonneg_right (mul_nonneg (pow_nonneg (add_nonneg zero_le_one hx) _) (zero_le_one.trans (rated ..)))
   exact (value_t h.bound hX (A.tan i)).trans (calc bloom G r*(t*A.momentum)= (bloom G r*A.momentum)*t := by ring
                                                         _≤ _:= mul_le_mul_of_nonneg_right hU' ht)
 rw [one_pow,mul_one]; have hP:=rated G k r; have hy: w^(q+1)≤ (1+w)^k:= le_trans (pow_le_pow_left₀ hx (le_add_of_nonneg_left zero_le_one) _) (pow_le_pow_right₀ (le_add_of_nonneg_right hx) hlq); have hh:t^(q+1) ≤ t:= by rw [pow_succ]; exact mul_le_of_le_one_left ht (pow_le_one₀ ht hk)
 apply (hm.order (q+1) hlq).trans
 change rate G k r*(w*t)^(q+1) ≤ _
 rw [mul_pow,← mul_assoc]; refine mul_le_mul ((mul_le_mul_of_nonneg_left hy (zero_le_one.trans hP)).trans ?_) hh (pow_nonneg ht _) (fog G k r A.momentum hd); rw [mul_comm]; exact le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans (springGe ..)) (Nat.cast_nonneg _))

noncomputable abbrev weather (G:Gauge)(k r s:ℕ)(d:ℝ)(p:ℕ) := (cloud G k r d p)^s * (1+(s:ℝ))^k
lemma refresh : Brush k (A.sizeC*t^n*(weather G k r n d A.momentum)) 1 (A.read x r ∘ U) y:= by
 let C :ℝ:= cloud G k r d A.momentum; let X(i:Fin n)(z:E):= amend G r (A.tan i) (travel (U z) x (A.maps i).tour); let u (b: Ink G n)(y:E):= ∏ i:Fin n, X i y (b i)
 have hh (b:Ink G n): Brush k ((C*t)^n) n (u b) y:= by simpa [u,C, X] using! (Brush.all_prod univ (fun i:Fin n=> fun y=> X i y (b i)) (fun _=> C*t) (fun _=>1) (fun j _=> colorEvaluated (b j) (breath l A x r hd ht hk hv hU j)))
 let h:= Brush.spree Finset.univ _ _ (Nat.cast_nonneg n) (fun i _=> (hh i).smul (A.ink i))
 rw [← sum_mul] at h; rw [show A.read x r ∘ U=(fun y:E=>∑ i:Ink G n,A.ink i • u i y) from funext fun y=> A.globe x (U y) r]; refine h.trim.climb (le_of_eq ?_) le_rfl; rw [mul_pow]; unfold C weather; simp_rw [sizeC, ← Real.norm_eq_abs]; ring
end smooth
lemma weather_ge (G:Gauge) (k r s:ℕ)(d:ℝ) (n:ℕ) (hu:0≤d):0≤weather G k r s d n:=by unfold weather; have hv:=fog G k r n hu; positivity
open ConnectedActivityE6.Blaze.March
private noncomputable def current (G:Gauge) (j:ℕ):= (oar G j).choose
noncomputable def rune (G:Gauge)(j:ℕ):= 1+j*current G j
lemma rune_pos (G:Gauge)(j:ℕ):0<rune G j:= by unfold rune current; have hx:0<(oar G j).choose:=(oar ..).choose_spec.1; positivity
noncomputable abbrev shoot (G:Gauge)(k r s:ℕ)(p:ℕ):= weather G k r s (rune G k) p
noncomputable def flood (p:BudgetPoint)(k:ℕ)(r m:ℕ) (G:Gauge) (d a: ℕ):= (1+(d:ℝ)+a)^(p.power*k) * (shoot G k r m d)
private noncomputable abbrev Uc (p:BudgetPoint) (g:Gauge):= p.threshold*rune g p.order
local notation "ℓ"=> p.order
private lemma statement (hx:Healthy p.threshold (cone l A x) W): Ore W (A.read x r) (p.threshold*rune G p.order) (A.sizeC*p.threshold^n * (shoot G p.order r n A.momentum)) p.order := by intro E _ _ _ f a ha; rw [← ha] at hx; exact refresh l A x r (rune_pos _ _).le p.threshold_pos.le p.threshold_le hx
lemma autumn : p.Regular (A.cone l x) (A.read x r) := by
 have hh (U:Config G c)(he:Healthy p.threshold (A.cone l x) U): ContDiffAt ℝ (↑p.order) ((A.read x r) ∘ increment U) 0:= charted (statement l A x U p r he) (mul_pos p.threshold_pos (rune_pos ..))
 exact ⟨A.located l x r,(A.cont_ x r).measurable, A.legitimate x r,hh,fun i hi a l hl=> Next.Foundations.left_has a hl (hh i hi)⟩
lemma flood_ge (p:BudgetPoint)(k r m:ℕ)(G:Gauge)(d a:ℕ):0≤flood p k r m G d a:= mul_nonneg (pow_nonneg (by positivity) _) (weather_ge _ _ _ _ _ _ (rune_pos _ _).le)
lemma consulted (hz:separation x o≤ i) : p.supBounds o (A.cone l x) (A.read x r) (A.sizeC*p.threshold^n*flood p p.order r n G A.momentum i) := by
 let B:ℝ:= 1+A.momentum+i; have hh:1≤B:= le_trans (le_add_of_nonneg_right (Nat.cast_nonneg A.momentum)) (le_add_of_nonneg_right (Nat.cast_nonneg i)); let a:= current G p.order; let t:=p.threshold; have hp:0<t:=p.threshold_pos; have hD:0≤a:= (oar G p.order).choose_spec.1.le; let C:=shoot G p.order r n A.momentum
 have hr:Sailor G p.threshold (a*t) p.order:= ⟨fun c=> (oar ..).choose_spec.2 c p.threshold hp.le⟩
 refine ⟨mul_nonneg (mul_nonneg A.nn_size (pow_nonneg hp.le n)) (flood_ge ..),fun U hu l' hx hz'=>?_⟩
 have hb(y:Site c)(hy:y∈cone l A x):1+(separation y o:ℝ)≤B:= by unfold B; rw [add_assoc]; apply add_le_add_right; exact_mod_cast (separation_triangle y x o).trans (add_le_add ((separation_comm ..).trans_le (radius l A x y hy)) hz)
 have hT : (p.order:ℝ)*(a*t) ≤ p.threshold * rune G ℓ:= by unfold rune; dsimp only [t,a]; linarith only [p.threshold_pos]
 exact le_trans (costsD (A.located l x r) hr (mul_nonneg hD hp.le) o _ hT (statement l A x U p r hu) hb hh l' hx hz') (le_of_eq (by unfold flood B; ring)) -- h0 p.order manuscript req any etc.
end YM.Qlocal.Quipu.Sonnet.Vase
