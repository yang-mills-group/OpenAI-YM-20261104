import YM.RG01.Kernel.Wheel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
/-! # Probability perturbation, quotient, explicit mixed derivative and real Brush license.

Wheel angular prices include all factors already on the conditional numerator;
relative submargins: only need the actual CONSTANT term of denominator
positive (unmarked conditional supply). Use β costs only for altered factors.
This file works even on schedules where chart widths haven't been additionally
purchased; `Wheel` entries genuine and measurable even over hard regions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset
open ConnectedActivityE6.Blaze
open scoped Topology ContDiff BigOperators Classical
variable {κ Ω:Type}[Fintype κ][MeasurableSpace Ω]{μ:Measure Ω}
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
variable {w:κ→Ω→ℝ}(H : Caliber w μ) {Z:κ→Ω→ E→L[ℂ] ℂ}{K:ℝ} (L:Wheel μ Z K)
variable {F:κ→Ω→ℂ}{b:ℝ}(he:Bounded μ F b)
namespace Wheel
abbrev GΩ := generating w Z μ
def quota (w:κ→Ω→ℝ)(Z:κ→Ω→ E→L[ℂ] ℂ)(μ: Measure Ω)(F:κ→Ω→ℂ) := generating w Z μ F / generating w Z μ 1
open Kernel
include H L
omit L in
lemma base : generating w Z μ 1 (0:E) = 1:=by simp only [generating,map_zero,Complex.exp_zero,mul_one,H.unit]
lemma base_nonzero {z:E}(h:∀ i x,‖Z i x z‖ ≤ 1/4):
    1/2≤‖generating w Z μ 1 z‖:=by
  have hx:(1:κ→Ω→ℂ)=1:=rfl
  have he i x: ‖(1:κ→Ω→ℂ) i x*Complex.exp (Z i x z) - 1‖ ≤ 1/2:=by
    rw [Pi.one_apply,Pi.one_apply,one_mul]
    have hh:=h i x
    have hS:=Complex.norm_exp_sub_one_le (x:=Z i x z) (hh.trans (by norm_num))
    linarith only [hS,hh]
  unfold generating
  have hh := H.decrease (F:=fun i u=> (1:κ→Ω→ℂ) i u*Complex.exp (Z i u z)) 1 (show Bounded μ _ (1/2) from ⟨fun i=> by
    change AEStronglyMeasurable (fun u=>1*Complex.exp (Z i u z)-1) μ
    exact (aestronglyMeasurable_const.mul (Complex.continuous_exp.comp_aestronglyMeasurable (L.measurable i z))).sub aestronglyMeasurable_const, he⟩) (show Bounded μ (1:κ→Ω→ℂ) 1 from ⟨fun i=> aestronglyMeasurable_const,fun i x=> le_of_eq norm_one⟩)
  rw [H.unit] at hh; have ht := norm_sub_norm_le (1:ℂ) (moment w μ (fun i u=> (1:κ→Ω→ℂ) i u*Complex.exp (Z i u z)))
  rw [norm_one,norm_sub_rev] at ht; linarith

include he
variable (hb:0≤b)
include hb
lemma nonvanish {z:E}(h:∀ i x, ‖Z i x z‖ ≤ 1/4):
    AnalyticAt ℂ (quota w Z μ F) z ∧ ‖quota w Z μ F z‖ ≤ 2*(b*Real.exp (1/4)):=by
  let G:=generating w Z μ
  have ht:=L.base_nonzero H h; have hp:0 < ‖G 1 z‖:= lt_of_lt_of_le (by norm_num) ht
  have hg:‖G F z‖≤ b*Real.exp (1/4):=H.price (L.tilt_charge he z (1/4) (by norm_num) h hb)
  unfold quota; refine ⟨(L.entire H he hb z (Set.mem_univ _)).div (L.entire H (F:=1) (b:=1) ⟨fun i=>aestronglyMeasurable_const,fun i x=>le_of_eq norm_one⟩ zero_le_one z (Set.mem_univ _)) (norm_ne_zero_iff.mp hp.ne'),?_⟩
  change ‖G F z / G 1 z‖ ≤ _; rw [norm_div, div_le_iff₀ hp]
  apply hg.trans; have he:=Real.exp_pos (1/4)
  change _ ≤ 2 * (_ * _)* _; change _≤ ‖G 1 z‖ at ht; nlinarith [mul_nonneg hb he.le]

variable [NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
lemma real_derivative (k:ℕ)(x:Fin k→E): iteratedFDeriv ℝ k (generating w Z μ F) 0 x=moment w μ (carrier Z F x):=by
  have hp := (L.entire H he hb).contDiff (n:=(↑k : WithTop ℕ∞))|>.contDiffAt (x:=0)
  rw [← hp.restrictScalars_iteratedFDeriv (𝕜:=ℝ)]
  exact L.atZero H he hb ..
lemma rawBrush (k:ℕ):Brush k b K (generating w Z μ F) 0:=by
  refine ⟨(((L.entire H he hb|>.contDiff (n:= (↑k:WithTop ℕ∞)))|>.restrict_scalars ℝ).contDiffAt),L.sign,fun j hj=> ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hb (pow_nonneg L.sign _)) fun m=>?_⟩
  rw [L.real_derivative H he hb ..]
  exact H.price (L.pay_norm he m hb)

-- constants uniform over all E, κ, Ω; chooses only one standard inverse function near 1.
omit H L he hb in
lemma inverse_cost (k:ℕ):∃ B:ℝ,0≤ B ∧ Brush k B 1 (Inv.inv:ℂ→ℂ) 1:=by
  obtain ⟨C,h,hP⟩:= Brush.neighborhood (f:=(Inv.inv : ℂ→ℂ)) (k:=k) 1 (by fun_prop (disch:=norm_num))
  exact ⟨C,h.le,hP.self_of_nhds⟩
def invoice (k :ℕ)(b:ℝ):= b * ((k.factorial:ℝ)*(inverse_cost k).choose)
lemma receipt (k:ℕ): Brush k (invoice k b) (K+2*K) (quota w Z μ F) 0:= by
  let f:=generating w Z μ 1; let U:=(inverse_cost k).choose
  have hn : Brush k 1 K f 0:= L.rawBrush H (b:=1) (show Bounded μ (1:κ→Ω→ℂ) _ from ⟨fun i=>aestronglyMeasurable_const,fun i x=>le_of_eq norm_one⟩) zero_le_one k
  have hi: Brush k U 1 (Inv.inv:ℂ→ℂ) (f 0):= by unfold f; rw [Wheel.base H]; exact (inverse_cost k).choose_spec.2
  have hh := (L.rawBrush H he hb k).paints (hn.pine hi)
  have heq : quota w Z μ F = (fun i=> generating w Z μ F i *(f i)⁻¹):=by funext; rw [quota,Pi.div_apply,div_eq_mul_inv]
  rw [heq]; simpa only [one_add_one_eq_two] using! hh
end Wheel
end YM.RG01.Kernel
