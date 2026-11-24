import YM.PertExtension.OrbExpansion
import YM.FormalOPE.RG10.StationaryMarks.Asympt
/-!
# Gauge-section Laplace test at a fixed period

Arbitrary compact-window shapes near vacuum, local smooth germs only. No assumption about full
Landau surface being a section. Coefficients defined by moments; this is used for identification.
This doesn't request any joint n→∞ asymptotics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Laplace
open Function Set Filter Metric MeasureTheory Measure PertExtension Series Radial Series.Tested
open scoped ContDiff Topology Classical BigOperators
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
structure Steep (f:E→ℝ) : Prop extends Stationary f where
 gap : ∃ c>0,∀ u : E,c*‖u‖^2 ≤ jet f 2 u
variable {f K a b:E→ℝ}
omit [FiniteDimensional ℝ E] in
lemma jet_germ (h:f=ᶠ[𝓝 0] a): jet f=jet a:= by funext i u; unfold jet; rw [(h.iteratedFDeriv (𝕜:=ℝ) i).self_of_nhds]
omit [FiniteDimensional ℝ E] in
lemma Steep.germ (p:Steep f) (h:f=ᶠ[𝓝 0] a) : Steep a:=
 ⟨⟨p.smooth.congr_of_eventuallyEq h.symm,h.self_of_nhds.symm.trans p.base0,fun u=>by rw [←jet_germ h,p.base1]⟩,by rw [←jet_germ h]; exact p.gap⟩
lemma rem (p:Steep f) : ∃ c>0,∀ᶠ x:E in 𝓝 0,c*‖x‖^2 ≤ f x:= by
    obtain ⟨c,hc,h⟩:=p.gap; let d:=c/2; have hd:0<d:=half_pos hc
    obtain ⟨r,C,hr,_,H⟩:=p.toStationary.dominated hd
    refine ⟨d,hd,?_⟩; filter_upwards [closedBall_mem_nhds (0:E) hr] with x hx
    have hp:= (H x 1 one_pos ((one_mul _).trans_le (mem_closedBall_zero_iff.mp hx))).2; simp only [higher,one_smul,one_pow,div_one,Real.norm_eq_abs] at hp
    have hu:= (le_abs_self _).trans hp; unfold d at *; linarith [h x]

omit [FiniteDimensional ℝ E] in
lemma nearby (h:ContDiffAt ℝ ∞ K 0): ∀ᶠ x in 𝓝 (0:E), ContinuousAt K x:= ((h.of_le (show (0:WithTop ℕ∞) ≤ ∞ from bot_le)).eventually (by simp)).mono (fun x hx=> hx.continuousAt)
lemma canonical (p:Steep f)(k:ContDiffAt ℝ ∞ K 0): ∃ r>0, let D:=closedBall (0:E) r; ContinuousOn f D ∧ ContinuousOn K D ∧ (∃ c>0,∀ x∈D,c*‖x‖^2 ≤ f x):= by
    obtain ⟨c,hc,H⟩:=rem p
    obtain ⟨δ,hδ,G⟩:= Metric.mem_nhds_iff.mp (H.and ((nearby p.smooth).and (nearby k)))
    have he:= Set.Subset.trans (closedBall_subset_ball (half_lt_self hδ) (x:=(0:E))) G
    exact ⟨δ/2,half_pos hδ,fun x hx=> (he hx).2.1.continuousWithinAt, fun x hx=>(he hx).2.2.continuousWithinAt,c,hc,fun x hx=>(he hx).1⟩
variable [MeasurableSpace E][BorelSpace E]
variable (μ:Measure E)[μ.IsAddHaarMeasure]
local notation "d" => Module.finrank ℝ E
def envelope (K f : E→ℝ)(t:ℝ)(x) := K x * Real.exp (-f x/t^2)
/-- Common extracted scalar power. -/
def reading (S:Set E) (K f : E→ℝ)(t:ℝ) := (t^d)⁻¹ * ∫ x in S,envelope K f t x ∂μ
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma replace (h:f=ᶠ[𝓝 0] a)(k:K=ᶠ[𝓝 0] b) : moment μ K f= moment μ b a:=by
 funext x; unfold moment normTerm kernel integrandSeries layers; rw [jet_germ h,jet_germ k]
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma reading_germ {S:Set E}(p:MeasurableSet S)(hf:EqOn f a S)(hk:EqOn K b S) : reading μ S K f=reading μ S b a:= by
 funext t; refine congr_arg ((t^d)⁻¹ * ·) (setIntegral_congr_fun p ?_); intro x hx; unfold envelope; rw [hf hx,hk hx]
lemma reading_ball {r t:ℝ}(h:0<t) : reading μ (ball 0 r) K f t=partialSum μ K f r t:=by
 let g:= envelope K f t; let S:= ball (0:E) r; let A:=S.indicator g
 have he(u:E): A (t • u)=(disc t r).indicator (fun x=> g (t • x)) u:= by
    unfold A; by_cases hx:t • u∈S;rw [indicator_of_mem hx, indicator_of_mem (show u∈disc t r from hx)]
    rw [indicator_of_notMem hx, indicator_of_notMem (show u∉disc t r from hx)]
 have hv (u:E) : g (t • u)= projection K f t u:= (projection_eq K f t u).symm
 change _ * (∫ u in S,g u ∂μ)= ∫ u in disc t r, _ ∂μ; rw [←integral_indicator (s:=S) isOpen_ball.measurableSet, ←smul_eq_mul, ← Measure.integral_comp_smul_of_nonneg μ A t (hR:=h.le)]; simp_rw [he,hv]; exact integral_indicator (disc_meas ..)
-- small window, without globally measurable assumptions
lemma inside {ρ:ℝ}(p:Steep f)(h:ContDiffAt ℝ ∞ K 0) (hf:ContinuousOn f (closedBall 0 ρ))(hK:ContinuousOn K (closedBall 0 ρ)) (hr:0<ρ)(n:ℕ): ∃ r>0,∀ ε∈Ioo 0 (min r ρ),Tested.Bill (n+1) (reading μ (ball 0 ε) K f-peval (moment μ K f) n):= by
 let S:=closedBall (0:E) ρ; let a':=S.indicator f; let b':=S.indicator K; have hmS:MeasurableSet S:= isClosed_closedBall.measurableSet; have ha:Measurable a':= hf.measurable_piecewise continuousOn_const hmS; have hb:Measurable b':= hK.measurable_piecewise continuousOn_const hmS
 have he : ∀ᶠ x:E in 𝓝 0,x∈ S:= closedBall_mem_nhds 0 hr; have hφ : f=ᶠ[𝓝 0] a':= he.mono (fun x hx=> (indicator_of_mem hx f).symm); have hψ : K=ᶠ[𝓝 0] b':= he.mono (fun x hx=> (indicator_of_mem hx K).symm); obtain p':= p.germ hφ
 obtain ⟨r,h',H⟩:= p'.toStationary.rescale_estimate μ (h.congr_of_eventuallyEq hψ.symm) hb ha p'.gap n; refine ⟨r,h',?_⟩
 intro c hc; obtain ⟨C,hC⟩:= H c ⟨hc.1,(lt_min_iff.mp hc.2).1⟩; have hv : ball (0:E) c ⊆ S:= ball_subset_closedBall.trans (closedBall_subset_closedBall (lt_min_iff.mp hc.2).2.le); rw [replace μ hφ hψ, reading_germ μ (a:=a') (b:=b') isOpen_ball.measurableSet (fun x hx=>(indicator_of_mem (hv hx) f).symm) (fun x hx=>(indicator_of_mem (hv hx) K).symm)]
 refine ⟨|C|,abs_nonneg _,?_⟩; filter_upwards [hC, Tested.eventually_pos] with t ht hu; rw [Pi.sub_apply,reading_ball (f:=a') (K:=b') μ hu]; exact ht.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hu.le _))
omit [BorelSpace E] in
lemma shell {S:Set E}{ρ r:ℝ}(p:ContinuousOn K (closedBall 0 ρ))(hf : ∃ c>0,∀ x∈closedBall (0:E) ρ,c*‖x‖^2 ≤ f x)(hr:0<r)(hρ:0<ρ)(hS:S⊆closedBall 0 ρ) (n:ℕ) : Tested.Bill n (reading μ (S \ ball 0 r) K f):= by
 obtain ⟨c,hc,h⟩:=hf; let T:= closedBall (0:E) ρ; let a:=c*r^2; have ha: 0<a:=by unfold a; positivity
 obtain ⟨M,hM⟩:= (isCompact_closedBall ..).exists_bound_of_continuousOn p; have hM':0≤M:= (norm_nonneg _).trans (hM 0 (mem_closedBall_self hρ.le))
 obtain ⟨R,hR,H⟩:= FormalOPE.RG10.StationaryMarks.rapid ha d n; let U:=S \ ball 0 r
 refine ⟨ μ.real U * M * R, by positivity,?_⟩; filter_upwards [Tested.eventually_pos] with t ht
 let k:= M * Real.exp (-a/t^2); have ho: μ U< ⊤ := (measure_mono (Set.sdiff_subset (s:=S) (t:=ball 0 r) |>.trans hS)).trans_lt ((isCompact_closedBall (0:E) ρ).measure_lt_top)
 have he (x:E)(hx:x∈U): ‖envelope K f t x‖ ≤ k:= by
    have hi:=hS hx.1; have hr:r ≤ ‖x‖:= not_lt.mp (hx.2 ∘ mem_ball_zero_iff.mpr)
    have ha:a≤f x:= (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr _) hc.le).trans (h x hi); unfold envelope; rw [norm_mul,Real.norm_eq_abs (Real.exp ..),abs_of_pos (Real.exp_pos _)]; exact mul_le_mul (hM _ hi) (Real.exp_le_exp.mpr (by gcongr)) (Real.exp_pos _).le hM'
 unfold reading; rw [norm_mul,Real.norm_eq_abs ((t^d)⁻¹), abs_of_nonneg (by positivity)];
 calc
   _ ≤ (t^d)⁻¹ * (k * μ.real U) := mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const ho he) (by positivity)
   _ = μ.real U * M * ((t^d)⁻¹*Real.exp (-a/t^2)):= by ring
   _ ≤ _ := by rw [mul_assoc (μ.real U * M) R]; exact mul_le_mul_of_nonneg_left (H _ ht) (by positivity)
-- all suff. small windows
lemma on_patch (p:Steep f)(h:ContDiffAt ℝ ∞ K 0): ∃ U ∈ 𝓝 (0:E),∀ S ∈ 𝓝 (0:E), MeasurableSet S → S ⊆ U → Tested.Aspiration (reading μ S K f) (moment μ K f):= by
 obtain ⟨r,hr,hf,hK,hD⟩:= canonical p h; let T:=closedBall (0:E) r; refine ⟨T, closedBall_mem_nhds 0 hr,?_⟩; intro S hS hS' hs n
 obtain ⟨ε,he,H⟩:= inside μ p h hf hK hr n; obtain ⟨b,hb,hB⟩:= Metric.mem_nhds_iff.mp hS
 let δ:=min b (min ε r)/2; have hd':0<min b (min ε r):=lt_min hb (lt_min he hr); have hd:0<δ:=half_pos hd'; have hdq:δ<min b (min ε r):= half_lt_self hd'
 let W:=ball (0:E) δ; have hw:W ⊆ S:= (ball_subset_ball (lt_min_iff.mp hdq).1.le).trans hB; have hT (t:ℝ): IntegrableOn (envelope K f t) T μ:= ((hK.mul (Real.continuous_exp.continuousOn.comp (hf.neg.div_const _) (Set.mapsTo_univ ..))).integrableOn_compact (isCompact_closedBall ..))
 let a := reading μ W K f; let b':=reading μ (S \ W) K f; have hq : reading μ S K f - peval (moment μ K f) n = (a-peval (moment μ K f) n)+ b' := by
    suffices he: reading μ S K f=a+b' by rw [he]; abel
    funext t; have hx:= setIntegral_union (μ:=μ) (f:=envelope K f t) (show Disjoint W (S\W) from disjoint_sdiff_right (s:=W) (t:=S)) (hS'.diff isOpen_ball.measurableSet) ((hT t).mono_set (hw.trans hs)) ((hT t).mono_set (Set.sdiff_subset.trans hs)); rw [union_comm W,sdiff_union_of_subset hw] at hx; rw [Pi.add_apply,reading]; unfold a b' reading; rw [hx,mul_add]
 rw [hq]; exact Tested.bill_add (H δ ⟨hd,(lt_min_iff.mp hdq).2⟩) (shell μ hK hD hd hr hs _)
end YM.FVA2.Laplace
