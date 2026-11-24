import YM.Comparison.RG02.Laplace.Fleet
/-!
# Vacuum projection on regulator-through-order

 Use comparison BEFORE (`Order.before`) on actual real axis. Here specifically no volume
 estimate; `Test` requires the scaled vacuum actually has the leading constant & higher
 coefficients. For application to any extensive growth this port can be inappropriate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace.Fleet
open Function Filter Finset MeasureTheory RG
open Marker Multi Order PertExtension.Series PertExtension.Series.Tested
open YM.Extra.Trajectories (connected part_sub)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {F : ℝ→Poly R} {r : ℕ} {X : Grade R r}
local notation "P"=> Poly R
local notation "C"=> R.quiet
local notation "R₀"=> (1:V→ℝ)

-- all-negative `Real.log` domain issues separate; eventually unimportant for Test because leading one.
variable (h : UnitLeading X) (hx : Test X F) (hp : Symmetric X) (hk : Simple X)

private lemma unit_peval (X : Grade R r) : Trial (detail X C) (fun t=> (value (t:ℂ) X).part C) r:=by unfold Trial; simp_rw [← tests]; rw [show (fun t => peval (detail X C) r t)= peval (detail X C) r from rfl,sub_self]; exact bill_zero
include h hk
private lemma ratio_margin : Bill 1 (fun t=>1 - unmarked X t) := by
   obtain ⟨c,hc,hB⟩:= trial_earlier (m:=0) (Nat.zero_le _) (unit_peval X)
   refine ⟨c,hc,hB.mono fun t ht=>?_⟩
   rw [norm_sub_rev]; rw [Pi.sub_apply, ← pure_vacuum X hk t, peval, Zone.eval] at ht
   simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, one_smul, tests_origin X h] at ht; rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real] at ht; exact ht
include hx
omit hk in
private lemma positive_real {b : ℝ} (he : b<1) : ∀ᶠ t in along, b ≤ ((F t).part C).re ∧ b ≤ unmarked X t := by
    have hl {x : ℝ→ℂ} (h : Tendsto x along (𝓝 1)) : ∀ᶠ t in along, b≤ (x t).re := by
       have hf : Tendsto (Complex.re ∘ x) along (𝓝 1):= (Complex.continuous_re.tendsto (1:ℂ)).comp h
       filter_upwards [hf.eventually (lt_mem_nhds he)] with t hi; exact le_of_lt hi
    exact (hl (arriving h hx)).and (hl (tests_origin X h ▸ trial_sample (unit_peval X))) -- latter no hk?...

include hp
lemma scalar : Trial (detail (logVac X) C) (fun t=> (Real.log ((F t).part C).re : ℂ)) r := by
   obtain ⟨C',hc,hC⟩:= hx C; obtain ⟨b,hb,hH⟩:= ratio_margin h hk; let ε:ℝ:= 1/2
   have he: 0<ε:= half_pos one_pos; have h0: ε< 1:= by norm_num [ε]
   let z:= Order.subtotal R₀ r 1 (logSeries r (render (denominator X))); let m:= C' + ε*(b^(r+1)/ε+max z 0)
   refine ⟨m/ε,by unfold m; positivity,?_⟩
   -- sufficiently small as fixed regulator, even if r=0
   have hg (v : ℝ):= exponent_marked X h hk v
   have hh(i : ℝ) : (value (i:ℂ) (logVac X)).part C=Complex.ofReal (exponentPrice X i):=by rw [hg]; change (Poly.send C _).part C=_; simp
   filter_upwards [hC, Tested.eventually_small (t:=1) one_pos, positive_real h hx h0,hH,Tested.eventually_top (show 0 < ε/(b+1) by positivity)] with t ht hi hl he' hk'
   let V := ((F t).part C).re; let U := unmarked X t
   have hm:= (lt_div_iff₀ (by positivity:0<b+1)).mp hk'
   have hv:=hi.1; have ha: |t|=t:=abs_of_pos hv
   change ‖1-U‖≤ b * t^1 at he'; rw [Real.norm_eq_abs,pow_one] at he'
   have hpU : |1-U|≤ε:=he'.trans (le_of_lt (by linarith))
   have hπ:= before X h hp hk t 1 (by rw [ha]; exact hi.2.le) R₀ (fun _=>one_pos) V ε he (hpU.trans_lt h0) hl.1 hl.2
   have hO:= Complex.abs_re_le_norm ((F t).part C- (Order.value (t:ℂ) X).part C)
   rw [Pi.sub_apply,tests] at ht
   have hd: |V-U| ≤ C'*t^(r+1):=hO.trans ht
   rw [Pi.sub_apply,tests,hh]; change ‖(Real.log V : ℂ)-_‖ ≤ _; rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
   rw [ha] at hπ
   apply le_of_mul_le_mul_left _ he
   calc
    _ ≤ _:= hπ
    _ ≤ C'*t^(r+1)+ ε * ((b*t)^(r+1)/ε + t^(r+1)*max z 0) := by
       refine add_le_add hd (mul_le_mul_of_nonneg_left (add_le_add ?_ (mul_le_mul_of_nonneg_left (le_max_left ..) (pow_nonneg hv.le _))) he.le)
       refine div_le_div₀ (by unfold U at *; positivity) (pow_le_pow_left₀ (abs_nonneg _) he' _) he ?_; unfold ε at *; linarith only [hpU]
    _ = ε*(m/ε*t^(r+1)) := by unfold m ε; rw [mul_pow]; ring
end YM.Comparison.RG02.Laplace.Fleet
