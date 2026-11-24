import YM.FormalOPE.RG10.StationaryMarks.Calendar
/-!
 # Taylor accuracy relative to Marked Σ on the same measure.

 Does not use any claim of working in varying matrix determinant. Uses downward insertion costs
 and forest joint integral. All constants local finite data.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {I J:Type}[Fintype I][Fintype J]
local notation "μ"=> physical G I
namespace Survey.Ready
variable {P:ChartRatio G}{U:Survey G I J}{O: Spending G I}{w:J→ℝ→ℝ}
local notation "Z"=> (U.target)

omit [Fintype I] in
lemma press_body {t:ℝ}(ht:t≠0)(u:Configuration G I) : dollar (U.adjusted w t) O t u= dollar Z O t u * Real.exp (U.spike w t u):= by
 unfold dollar; rw [mul_assoc, ← Real.exp_add, U.spike_rate w ht, show -Z u/t^2+(Z u-U.adjusted w t u)/t^2= -U.adjusted w t u/t^2 from by field_simp; ring]

 def gap (U:Survey G I J) (w:J→ℝ→ℝ)(O:Spending G I)(k:ℕ)(t:ℝ)(u:Configuration G I) := dollar (U.adjusted w t) O t u - dollar U.target O t u * U.rubber w k t u -- bug local notation Z
variable (R:U.Ready)(h:Curtain O)(hs:∀ i,Tracks (w i) (U.w i))
local notation "A¼"=> ((4:ℝ)⁻¹ • Z)
include R h hs in
lemma body_budget (k:ℕ):∃ B:ℝ,0≤B ∧ ∀ᶠ t in Tested.germ,∀ u:Configuration G I,
 ‖gap U w O k t u‖ ≤ B*t^(k+1) * dollar A¼ 1 t u:= by
 obtain ⟨M,Hm⟩:=h.bounded; have hm:0≤M:=(norm_nonneg _).trans (Hm 1)
 obtain ⟨K,hk,Hk⟩:= R.rate_bound hs; obtain ⟨D,hd,Hd⟩:= Shed.seedling k
 refine ⟨M*D*K^(k+1),by positivity,?_⟩
 filter_upwards [Hk, Tested.eventually_small (show 0<(1 / (2*K+1):ℝ) from by positivity)] with t ht hh
 obtain ⟨ht',hu⟩:= hh; have hz:K*t≤ 1/2:=by nlinarith only [(lt_div_iff₀ (by positivity : (0:ℝ)<2*K+1)).mp hu,ht']
 intro u; let y := Z u/t^2; let F := Real.exp (-y); let a:=U.spike w t u
 have he: gap U w O k t u= O u * (F*(Real.exp a-referenceCharge k a)):= by rw [gap,press_body ht'.ne']; unfold dollar F rubber y a; rw [neg_div]; ring -- orientation
 have ha: 0≤y := div_nonneg (R.entire.nn u) (sq_nonneg _)
 have hy:= Hd a y (K*t) (by positivity) ha (R.spike_bill ht ht' u) hz
 calc
    _ ≤ M * (D*(K*t)^(k+1)*Real.exp (-y/4)) := by rw [he,norm_mul]; exact mul_le_mul (Hm u) hy (norm_nonneg _) hm
    _ = _ := by unfold y dollar; change _ = _ * ( (1:ℝ)*Real.exp (-( (4:ℝ)⁻¹*(Z u))/t^2)); rw [one_mul,show -(Z u/t^2)/4= -(4⁻¹ * Z u) /t^2 by ring,mul_pow]; ring

include R h in
lemma transgression_deduct {t:ℝ}(H:∀ i,0<w i t)(k:ℕ) : U.advanced w O t- U.partialAt w O k t= scale G I t * ∫ u,gap U w O k t u ∂μ:= by
 unfold advanced gap journal; rw [R.income h, ← mul_sub, integral_sub (R.curved h H) (R.enough h k w t)]

variable (L:LocalRatio P)
include L R h hs in
lemma transferBudget (k:ℕ):Tested.Bill (k+1) (U.advanced w O - U.partialAt w O k):= by
 have hu : Credential A¼:= guarded R.entire (by norm_num)
 obtain ⟨B,hb,Hb⟩:= R.body_budget h hs k
 obtain ⟨D,hd,HD⟩:= (base L hu Inherit.unit).bounded
 refine ⟨B*D,mul_nonneg hb hd,?_⟩; filter_upwards [Hb, HD,R.event hs,Tested.eventually_pos] with t ht hy hx hp
 rw [Pi.sub_apply,R.transgression_deduct h hx]
 have hq:0≤scale G I t:= by unfold scale; positivity
 have he : ‖∫ u,gap U w O k t u ∂μ‖ ≤ B*t^(k+1)* (∫ u,dollar A¼ (1:Spending G I) t u ∂μ) := by
   rw [← integral_const_mul]; exact norm_integral_le_of_norm_le ((endowment hu Inherit.unit t).const_mul _) (Filter.Eventually.of_forall ht)
 rw [norm_mul,Real.norm_of_nonneg hq]; refine (mul_le_mul_of_nonneg_left he hq).trans ?_
 rw [mul_left_comm, show B*D*t^(k+1)=B*t^(k+1)*D by ring]
 apply mul_le_mul_of_nonneg_left ?_ (by positivity)
 exact (Real.le_norm_self (journal A¼ 1 t)).trans (by simpa using hy)

include L R h hs in
lemma validated : Tracks (U.advanced w O) (U.imprint P O):= by
 intro n
 have ha:= R.transferBudget h hs L n; have hb:= R.allPlates h n hs L n
 have hv: (peval (term (U.imprint P O)) n)=peval (term (U.truncation P O n)) n:=funext fun t=> by unfold peval Zone.eval; apply Finset.sum_congr rfl; intro i hi; dsimp only; rw [R.pre_stall L h (n:=n) (j:=i) (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
 rw [hv]; convert bill_add ha hb using 1; rw [sub_add_sub_cancel]
end Survey.Ready
end YM.FormalOPE.RG10.StationaryMarks
