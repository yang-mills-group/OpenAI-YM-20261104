import YM.Integration.WilsonConditionalTaylorThermalMixedBook
import YM.Integration.WilsonConditionalTaylorThermalInteractionDifference

/-! In the signed, antisymmetric temperature tilt the first discarded
Boltzmann term has three score factors, hence six coupling orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalOddInsertion
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalWeight
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}

private theorem realTail (s : ℝ) : ‖Real.exp (-s)-1+s-s^2/2‖≤‖s‖^3*Real.exp ‖s‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((-s : ℝ):ℂ) 3
  simp only [←Complex.ofReal_exp,←Complex.ofReal_pow,←Complex.ofReal_natCast,←Complex.ofReal_div,
    ←Complex.ofReal_sum,←Complex.ofReal_sub,Complex.norm_real,norm_neg] at h
  have e : Real.exp (-s)-(∑i∈Finset.range 3,(-s)^i/i.factorial) = Real.exp (-s)-1+s-s^2/2 := by
    simp [Finset.sum_range_succ,Nat.factorial];ring
  rwa [e] at h

def tail (t : d.Tags) (a : ℕ→ℝ) (f : Config G n→ℝ) (y : Fields G d) :=
  let q := account t a y
  (Real.exp (-q)-1+q-q^2/2)*f (d.fine 1 y)

theorem smooth (ok : d.OK G) (t : d.Tags) (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) :
    d.SmoothAtFlat (tail t a f) := by
  let q := smoothAccount ok t a
  exact (((q.neg.exp.sub contDiffAt_const).add q).sub ((q.pow 2).div_const 2)).mul test.smooth

theorem late (ok : d.OK G) (t : d.Tags) (a : ℕ→ℝ) {f : Config G n→ℝ} {w : ℕ} (old : d.grade f w) :
    RadialOrder (6+w) (tail t a f ∘ d.tablePath) := by
  let A := account (G:=G) t a ∘ d.tablePath
  have head : A 0=0 := by simp [A,WilsonConditionalTaylorThermalWeight.account,tablePath_zero,account_flat ok]
  intro y
  apply bill_mul (f:=fun g => Real.exp (-A (g • y))-1+A (g • y)-(A (g • y))^2/2) _ (old y)
  obtain ⟨B,Bpos,bill⟩ := accountGrade ok t a y
  have tends := (directions (smoothAccount ok t a) y).tendsto_first
  change Tendsto (fun g : ℝ => A (g • y)) Tested.germ (𝓝 (jet A 0 y)) at tends
  rw [jet_zero,head] at tends
  have small := tends.norm.eventually (gt_mem_nhds (show ‖(0:ℝ)‖<1 by norm_num))
  refine ⟨B^3*Real.exp 1,mul_nonneg (pow_nonneg Bpos _) (Real.exp_nonneg _),?_⟩
  filter_upwards [small,bill] with g safe price
  change ‖A (g • y)‖≤B*g^2 at price
  calc
    _ ≤ ‖A (g • y)‖^3*Real.exp ‖A (g • y)‖ := realTail _
    _ ≤ (B*g^2)^3*Real.exp 1 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) price 3)
      (Real.exp_le_exp.mpr safe.le) (Real.exp_nonneg _) (pow_nonneg (mul_nonneg Bpos (sq_nonneg _)) _)
    _ = _ := by ring

def raw (P : ChartRatio G) (d : Descent n c) (a : ℕ→ℝ) (f : Config G n→ℝ) (k : ℕ) :=
  ∑t : d.Tags,gaussianTerm P t (score t a f) k

theorem before (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (a : ℕ→ℝ)
    {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) (k : ℕ) (hk : k<w+6) :
    bareRank P d a f k-bareRank P d (-a) f k = -(raw P d a f k+raw P d a f k) := by
  let ok := room_ok d room
  have each (t : d.Tags) :
      gaussianTerm P t (d.resetTerms a f t) k-gaussianTerm P t (d.resetTerms (-a) f t) k =
        -(gaussianTerm P t (score t a f) k+gaussianTerm P t (score t a f) k) := by
    have neg (y : Fields G d) : account t (-a) y = -account t a y := by
      change d.account (-(a)) t 1 y= -d.account a t 1 y
      rw [←zero_sub a,account_sub,account_zero,zero_sub]
    have eq : d.resetTerms a f t-d.resetTerms (-a) f t =
        (tail t a f-tail t (-a) f)-(score t a f+score t a f) := by
      funext y
      simp only [Pi.sub_apply,Pi.add_apply,tail,score,resetTerms,WilsonConditionalTaylorThermalWeight.account]
      rw [show d.account (-a) t 1 y= -d.account a t 1 y from neg y];ring
    have reset (z : ℕ→ℝ) : d.SmoothAtFlat (d.resetTerms z f t) := ((smoothAccount ok t z).neg.exp).mul test.smooth
    let sc : d.SmoothAtFlat (score t a f) := (smoothAccount ok t a).mul test.smooth
    have add := WilsonConditionalTaylorThermalInteractionDifference.linear P R room t (A:=score t a f+score t a f) (B:=score t a f) (sc.add sc) sc k
    rw [add_sub_cancel_right] at add
    rw [←WilsonConditionalTaylorThermalInteractionDifference.linear P R room t (reset a) (reset (-a)),eq,
      WilsonConditionalTaylorThermalInteractionDifference.linear P R room t
        (A:=tail t a f-tail t (-a) f) (B:=score t a f+score t a f)
        ((smooth ok t a test).sub (smooth ok t (-a) test)) (sc.add sc),
      WilsonConditionalTaylorThermalInteractionDifference.linear P R room t (smooth ok t a test) (smooth ok t (-a) test),
      gaussian_grade P R room (smooth ok t a test) (late ok t a old) t (by omega),
      gaussian_grade P R room (smooth ok t (-a) test) (late ok t (-a) old) t (by omega)]
    linarith
  simp only [raw,bareRank,Finset.sum_apply,←Finset.sum_sub_distrib,each,
    Finset.sum_neg_distrib,Finset.sum_add_distrib]

end YM.Integration.WilsonConditionalTaylorThermalOddInsertion
