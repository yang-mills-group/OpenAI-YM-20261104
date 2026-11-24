import YM.Comparison.RG02.Laplace.Trunc
import YM.Comparison.RG02.Order.VacLog
/-!
# Final operator on any finite-regulator Laplace test

 From component asymptotics, normalizing denominator and passing to logMark retains fixed
 order. Local analytic extension/frontier still owes all price estimates on actual schedule!
 This interface permits entirely pointwise asymptotic constants. Proves estimates for quotient and
 log retaining that through-r semantics. Does NOT supply a normed-activity-stability theorem. -/
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
local notation "B"=>Board R r
local notation "R₀"=> (1:V→ℝ)
-- support value only; no reserves
abbrev price (x : Poly R) := Poly.price (1:V→ℝ) x
def Test (X : Grade R r) (F : ℝ→ Poly R) := ∀ s:R.Mode, Trial (Laplace.detail X s) (fun t=> (F t).part s) r
omit [Fintype V] [DecidableEq V] in
private lemma pos (x : V) : 0<R₀ x:=zero_lt_one
omit [Fintype V] in
lemma as_sum (X : Poly R) : price X = ∑ i:R.Mode,‖X.part i‖ := by simp [price,Poly.price,Poly.toll]
omit [Fintype V] in
lemma price_nn (X : Poly R) : 0≤price X:= Poly.nonnegative pos _
lemma finance : Test X F ↔ Bill (r+1) (fun t : ℝ => price (F t - Order.value (t:ℂ) X)) := by
   constructor
   · intro h; let a(s:R.Mode) (v:ℝ):= ‖(F v - Order.value (v:ℂ) X).part s‖
     have he(s : R.Mode): Bill (r+1) (a s) := by
       obtain ⟨c,hc,H⟩:= h s; exact ⟨c,hc,H.mono fun i hi=> by simpa [a,part_sub, Real.norm_eq_abs,Laplace.tests] using hi⟩
     convert Laplace.bill_sum Finset.univ a (fun i _=> he i) using 1 -- infer univ
     · funext t; rw [as_sum,Finset.sum_apply]
   rintro ⟨c,hc,H⟩ s; refine ⟨c,hc,?_⟩
   filter_upwards [H] with t ht; rw [Real.norm_eq_abs, abs_of_nonneg (price_nn ..)] at ht
   rw [Pi.sub_apply,Laplace.tests]; change ‖(F t).part s-_‖ ≤ _; rw [← part_sub]; exact ((single_le_sum (fun i (_:i∈univ)=> norm_nonneg ((F t-Order.value (t:ℂ) X).part i)) (mem_univ s)).trans_eq (as_sum ..).symm).trans ht

-- eventual positive volume denominator portion retained with cancellations; may tend to huge
-- if g-scale/history not the fixed scalar. Here UnitLeading and Trial require common rescaling.
variable (h : UnitLeading X) (hx : Test X F)
include h hx
lemma arriving : Tendsto (fun t : ℝ=> (F t).part C) along (𝓝 1) := by simpa only [tests_origin _ h] using trial_sample (hx C)
private lemma receives (q : ℝ) (he : q < 1) : ∀ᶠ t in along, q ≤ ‖(F t).part C‖:= by
   have h1 := (arriving h hx).norm; rw [norm_one] at h1; filter_upwards [h1.eventually (lt_mem_nhds he)] with i hi; exact le_of_lt hi
omit h hx
private lemma value_cont (X : Grade R r) : Continuous (fun t:ℝ=> Order.value (t:ℂ) X) := by unfold Order.value; exact continuous_finsetSum _ fun i _=>Continuous.smul (Complex.continuous_ofReal.pow i) continuous_const
lemma bounded_price (X : Grade R r) : ∃ M : ℝ, 0≤M ∧ ∀ᶠ t : ℝ in along, price (Order.value (t:ℂ) X) ≤ M := by
   let X' (t : ℝ):= price (Order.value (t:ℂ) X)
   refine ⟨X' 0+1,add_nonneg (price_nn _) (by positivity), (show Tendsto X' along (𝓝 (X' 0)) from ((Poly.price_cont R₀).comp (value_cont X)).continuousAt.mono_left (by exact nhdsWithin_le_nhds) ).eventually (p:=fun t:ℝ=> t≤ X' 0+1) ?_⟩ -- Tendsto syntactic
   exact eventually_le_nhds (by simp [X'])
include h hx
variable (hs : Symmetric X)
include hs
lemma via : Test (Order.ratio X) (fun x => Order.unitScale (F x)) := by
   rw [finance]; let Q:= Order.ratio X; let T (t:ℝ):= Order.value (t:ℂ) X; let U (t:ℝ):= Order.value (t:ℂ) Q
   obtain ⟨M,hM,H⟩:= finance.mp hx
   obtain ⟨z,hz,he⟩:= bounded_price Q
   let ε:= (1/2:ℝ); have hε: 0<ε:=by norm_num [ε]
   have hk: ε< 1:=by norm_num [ε]
   let Z:= subtotal R₀ r 1 (render (denominator X) * render Q); let w:= M*(1+z)+max 0 Z
   refine ⟨w / ε,by unfold w; positivity,?_⟩
   filter_upwards [Tested.eventually_small (t:=1) one_pos, (receives h hx ε hk),H,he] with t ht hx hi hh
   let E:=F t-T t
   let R':= price (unitScale (F t)-U t); change ‖R'‖ ≤ _
   change price (U t)≤ z at hh; rw [Real.norm_of_nonneg (price_nn ..)] at hi; change price E ≤ _ at hi
   have hd:( F t|>.part C)≠0:=norm_pos_iff.mp (hε.trans_le hx)
   have hg:= ht.1; have hP:‖(t:ℂ)‖=t:=by simp [hg.le]
   have hp:= ratio_pay (x:=X) h hs (t:ℂ) (z:=1) (by rw [hP]; exact ht.2.le) (F t) E hd (by unfold E T; abel) hx R₀ pos
   rw [Real.norm_of_nonneg (show 0≤R' from price_nn _)]; apply le_of_mul_le_mul_left _ hε
   show ε * R' ≤ _
   calc
    _ ≤ price (E-E.part C • U t)+ t^(r+1)*Z:=by rwa [hP] at hp
    _ ≤ price E+price E*z+ t^(r+1)*max 0 Z := by
       have H0 : ‖E.part C‖≤ price E:= by rw [as_sum]; exact Finset.single_le_sum (fun i _=> norm_nonneg _) (Finset.mem_univ _)
       exact add_le_add ((priced_sub R₀ pos ..).trans (add_le_add le_rfl (by rw [Poly.adapted]; exact mul_le_mul H0 hh (price_nn _) (price_nn _)))) (mul_le_mul_of_nonneg_left (le_max_right ..) (pow_nonneg hg.le _))
    _ ≤ _ := by unfold w; specialize hi; rw [← mul_assoc ε, mul_div_cancel₀ _ hε.ne']; nlinarith [mul_le_mul_of_nonneg_right hi hz]

-- estimates in center-only (candidate analytic asserts separately), log uses same r
lemma connected_series : Test (logMarked X) (fun x=> connected (unitScale (F x))) := by
   let L:= unitScale ∘ F; let y := Order.ratio X
   let p (t:ℝ):= Order.value (t:ℂ) y
   obtain ⟨M,hM,hE⟩:= finance.mp (via h hx hs)
   obtain ⟨K,hK,h₀⟩:= bounded_price y
   let b:= Fintype.card V; have hb (x:R.Mode): x.val.card≤b:= card_le_univ _
   let B':=1+K+M; let T':=subtotal R₀ r 1 (logSeries (b+r) (render y)); have hc:0 ≤ B':=by unfold B'; positivity
   have hp := repeats_pos b B' hc
   refine finance.mpr ⟨repeats b B' * M + max 0 T',by positivity,?_⟩
   filter_upwards [hE,h₀, Tested.eventually_small (t:=1) one_pos, receives h hx (1/2) (by norm_num)] with t hi hk ht hz
   have hg:=ht.1; have hV:=ht.2.le
   have hT: ‖(t:ℂ)‖= t:=by simp [hg.le]
   have hZ (t : ℝ) (ht : (1/2:ℝ) ≤ ‖(F t).part C‖): (F t|>.part C)≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) ht)
   rw [Real.norm_of_nonneg (price_nn _)] at hi; change ‖price _‖ ≤ _; rw [Real.norm_of_nonneg (price_nn _)]
   change price (L t-p t) ≤ _ at hi
   have he: price (1-p t)≤1+K:= (priced_sub R₀ pos ..).trans (add_le_add (le_of_eq (Poly.one_price)) hk)
   have hl: price (1-L t) ≤ B':= by
      rw [show 1-L t= (1-p t)-(L t-p t) by abel]; apply (priced_sub R₀ pos ..).trans; exact add_le_add he (hi.trans (mul_le_of_le_one_right hM (pow_le_one₀ hg.le hV)))
   have hh:= log_mark_pay h hs (t:ℂ) (z:=1) (hT.symm ▸ ht.2.le) b hb (F t) (hZ _ hz) R₀ pos hl (he.trans (le_add_of_nonneg_right hM)) hi
   rw [hT] at hh; refine hh.trans ?_
   change _ + _* T' ≤ _; rw [add_mul,mul_assoc, mul_comm (max 0 T')]
   exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right ..) (pow_nonneg hg.le _))
end YM.Comparison.RG02.Laplace.Fleet
