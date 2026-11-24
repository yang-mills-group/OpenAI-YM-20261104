import YM.RGComparison.Core16.Wick
/-!
# Diagnostic: obtain nonzero leading coefficients *after* integration
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial GaussianScore
variable {G : Gauge} {n c : Side} {d : Descent n c} (t : d.Tags) (P : ChartRatio G) (R : LocalRatio P)
    {g : Config G n → ℝ} (hg : d.Testable g) {w : ℕ} (hG : d.grade g w) (u : ℕ → ℝ) (h : d.Room G)
local notation "E" => Coordinates G d

section calculus
lemma head_product {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {A f : Y → ℝ} (hc : ContDiffAt ℝ ∞ A 0) (he : ContDiffAt ℝ ∞ f 0)
    {k : ℕ} (hA : RadialOrder k A) (hf : RadialOrder w f) (x : Y) :
    jet (A * f) (k+w) x = jet A k x * jet f w x := by
  let z := directions (f:=A*f) (hc.mul he) x
  have H := congr_fun (z.unique ((directions hc x).prod (directions he x))) (k+w)
  dsimp only [conv,term] at H
  rw [PowerSeries.coeff_mul] at H; simp only [PowerSeries.coeff_mk] at H
  exact H.trans (Finset.sum_eq_single_of_mem (k,w) (Finset.mem_antidiagonal.mpr rfl) (fun i hi h => by
    by_cases hx : i.2<w
    · rw [jets_vanish he hf hx]; simp
    have hw := Finset.mem_antidiagonal.mp hi
    rw [jets_vanish hc hA (show i.1 < k from ?_)]; simp
    by_contra hT; apply h; ext1 <;> simp only <;> omega))
end calculus

include R hg h hG
lemma ordinary_grade_jet (x : E) :
    integrandSeries (phase G d t) (nearFee P t (d.resetTerms u g t)) w x =
      Chart.jacobian P (U:=d.Links) 0 * (Fintype.card d.Tags:ℝ)⁻¹ * jet (g ∘ d.fine 1 ∘ d.tablePath) w x := by
  let A (x : E) := Real.exp (- d.account u t 1 (d.tablePath x))
  let W (x : E) := Chart.jacobian P x * d.probability t (d.tablePath x) * A x
  have hA : ContDiffAt ℝ ∞ A 0 := ((account_smooth (room_ok d h) t u).of_le le_top).neg.exp
  have hb := prob_flat_tangent (room_ok d h) t
  have he := gaussian_origin P R h (Y := d.resetTerms u g t) (hA.mul hg.smooth) (w:=w) (fun v => by
    simpa only [Nat.zero_add] using! bill_mul (directions hA v).bounded (hG v)) t x
  rw [he, show nearFee P t (d.resetTerms u g t) = W * (g ∘ d.fine 1 ∘ d.tablePath) from
    funext (fun x => by unfold nearFee; rw [resetTerms]; exact (mul_assoc ..).symm)]
  have hh : ContDiffAt ℝ ∞ W 0 := (((Chart.Ratio.jacobian_smooth R).of_le le_top).mul
    (contDiffAt_const.congr_of_eventuallyEq hb)).mul hA
  have hr := head_product hh hg.smooth (k := 0) (fun x => (directions hh x).bounded) hG x
  rw [Nat.zero_add,jet_zero (f:=W)] at hr; rw [hr]
  unfold W A; rw [hb.self_of_nhds, tablePath_zero, account_flat (room_ok d h), neg_zero, Real.exp_zero,mul_one]

lemma ranking_positive (hp : ∀ x : E, 0 ≤ jet (g ∘ d.fine 1 ∘ d.tablePath) w x)
    {x : E} (hh : 0 < jet (g ∘ d.fine 1 ∘ d.tablePath) w x) :
    0 < ranking P d u g w := by
  have he : 0 < bareRank P d u g w := by
    rw [bareRank,Finset.sum_apply]; apply Finset.sum_pos _ Finset.univ_nonempty; intro t _
    have hT : 0 < Chart.jacobian P (U:=d.Links) 0 := Finset.prod_pos fun i _ =>
      (show 0 < Chart.fee P 0 from lt_max_of_lt_left (by rw [R.anchored,mul_one]; exact R.scale))
    have ha : 0 < (Fintype.card d.Tags : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance));
    let A := phase G d t
    unfold gaussianTerm Radial.moment; apply integral_pos_of_integrable_nonneg_nonzero (Smooth.continuousTerms ..)
      (integrates_term P R t (d.resetTerms u g t) h ((account_smooth (room_ok d h) t u |>.of_le le_top|>.neg.exp).mul hg.smooth) _) ?_ (x:=x)
    · unfold normTerm; rw [ordinary_grade_jet t P R hg hG u h]; exact (mul_pos (mul_pos (mul_pos hT ha) hh) kernel_pos).ne'
    intro y; unfold normTerm; rw [ordinary_grade_jet t P R hg hG u h]; exact mul_nonneg (mul_nonneg (mul_pos hT ha).le (hp y)) kernel_pos.le
  unfold ranking divide term
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (w,0) (Finset.mem_antidiagonal.mpr (add_zero w))]
  · dsimp only; simp only [PowerSeries.coeff_mk,PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_inv]; exact mul_pos he (inv_pos.mpr (pivot P R u h))
  intro j hj hk
  have hi := Finset.mem_antidiagonal.mp hj;
  rw [PowerSeries.coeff_mk,field_rank_zero P R h u hg hG _ (show j.1 < w from ?_),zero_mul]
  by_contra hL; apply hk; ext1 <;> simp only <;> omega
end YM.RGComparison.Core16.Descent
