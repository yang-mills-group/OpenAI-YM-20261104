import YM.RGComparison.Core16.Offset
import YM.RGComparison.Core16.Wick

/-! The temperature-dependent part of the genuine Core16 Laplace integrand.
At relative order two its exponential is linear in the whole signed account.
The first omitted term has four powers of the coupling in the original chart. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalWeight
open Lattice RG Tree Wilson Precision Push.BetaTransport RGComparison.Core16
open Function Filter MeasureTheory
open PertExtension PertExtension.Series Tested Radial
open scoped Topology ContDiff Classical BigOperators
open Descent
variable {G : Gauge} {n c : Side} {d : Descent n c}

/-- A finite temperature book has a bound on the very dates read by its action. -/
theorem finiteBand (d : Descent n c) (u : ℕ → ℝ) :
    d.Band (∑ j ∈ Finset.range (d.depth+1), ‖u j‖) u := by
  intro i hi
  exact Finset.single_le_sum (fun j _ => norm_nonneg (u j)) (Finset.mem_range.mpr (by omega))

def account (t : d.Tags) (u : ℕ → ℝ) (x : Fields G d) := d.account u t 1 x

def excess (t : d.Tags) (u : ℕ → ℝ) (x : Fields G d) : ℝ :=
  Real.exp (-account t u x) - 1 + account t u x

theorem accountGrade (ok : d.OK G) (t : d.Tags) (u : ℕ → ℝ) :
    RadialOrder 2 (account (G:=G) t u ∘ d.tablePath) := by
  let M := ∑ j ∈ Finset.range (d.depth+1), ‖u j‖
  have band : d.Band M u := finiteBand d u
  intro y
  obtain ⟨B,Bpos,bill⟩ := action_grade t ok y
  refine ⟨M*B,mul_nonneg (nonnegativeBand band) Bpos,?_⟩
  filter_upwards [bill] with g price
  change ‖d.action t 1 (d.tablePath (g • y))‖ ≤ _ at price
  rw [Real.norm_of_nonneg (action_nonneg ..)] at price
  exact (total_charge t band 1 (d.tablePath (g • y))).trans
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left price (nonnegativeBand band))

theorem smoothAccount (ok : d.OK G) (t : d.Tags) (u : ℕ → ℝ) :
    d.SmoothAtFlat (account (G:=G) t u) := (account_smooth ok t u).of_le le_top

theorem smoothExcess (ok : d.OK G) (t : d.Tags) (u : ℕ → ℝ) :
    d.SmoothAtFlat (excess (G:=G) t u) :=
  (((smoothAccount ok t u).neg.exp.sub contDiffAt_const).add (smoothAccount ok t u))

theorem excessGrade (ok : d.OK G) (t : d.Tags) (u : ℕ → ℝ) :
    RadialOrder 4 (excess (G:=G) t u ∘ d.tablePath) := by
  intro y
  obtain ⟨B,Bpos,bill⟩ := accountGrade ok t u y
  let A := account (G:=G) t u ∘ d.tablePath
  have h0 : A 0 = 0 := by simp only [A,Function.comp_apply,tablePath_zero,account,account_flat ok]
  have tends := (directions (smoothAccount ok t u) y).tendsto_first
  change Tendsto (fun g : ℝ => A (g • y)) Tested.germ (𝓝 (jet A 0 y)) at tends
  rw [jet_zero,h0] at tends
  have small := tends.norm.eventually (gt_mem_nhds (show ‖(0:ℝ)‖ < 1 by norm_num))
  refine ⟨B^2,sq_nonneg _,?_⟩
  filter_upwards [small,bill] with g safe price
  change ‖A (g • y)‖ ≤ B*g^2 at price
  have he := Real.norm_exp_sub_one_sub_id_le (x := -A (g • y))
    (by rw [norm_neg]; exact safe.le)
  rw [sub_neg_eq_add,norm_neg] at he
  exact he.trans ((pow_le_pow_left₀ (norm_nonneg _) price 2).trans_eq (by ring))

def extra (t : d.Tags) (u v : ℕ → ℝ) (f : Config G n → ℝ) (x : Fields G d) :=
  (excess t u x - excess t v x) * f (d.fine 1 x)

def score (t : d.Tags) (v : ℕ → ℝ) (f : Config G n → ℝ) (x : Fields G d) :=
  account t v x * f (d.fine 1 x)

theorem full (t : d.Tags) (u v : ℕ → ℝ) (f : Config G n → ℝ) :
    d.resetTerms u f t - d.resetTerms v f t =
      extra t u v f - score t (u-v) f := by
  funext x
  simp only [Pi.sub_apply,extra,score,excess,account,resetTerms,account_sub]
  ring

theorem smoothExtra (ok : d.OK G) (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    (test : d.Testable f) : d.SmoothAtFlat (extra t u v f) :=
  ((smoothExcess ok t u).sub (smoothExcess ok t v)).mul test.smooth

theorem extraGrade (ok : d.OK G) (t : d.Tags) (u v : ℕ → ℝ) {f : Config G n → ℝ}
    {w : ℕ} (grade : d.grade f w) : RadialOrder (w+4) (extra t u v f ∘ d.tablePath) := by
  intro y
  have h := bill_add (excessGrade ok t u y) (bill_neg (excessGrade ok t v y))
  simpa only [Nat.add_comm 4 w,Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using!
    bill_mul h (grade y)

theorem scoreGrade (ok : d.OK G) (t : d.Tags) (v : ℕ → ℝ) {f : Config G n → ℝ}
    {w : ℕ} (grade : d.grade f w) : RadialOrder (w+2) (score t v f ∘ d.tablePath) := by
  intro y
  simpa only [Nat.add_comm 2 w] using! bill_mul (accountGrade ok t v y) (grade y)

end YM.Integration.WilsonConditionalTaylorThermalWeight
