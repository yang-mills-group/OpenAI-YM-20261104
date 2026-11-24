import YM.RGComparison.Core16.Normalize

/-!
# Accounting for negative powers of coupling before quotient
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} {d : Descent n c} (P : ChartRatio G) (R : LocalRatio P)
    (h : d.Room G) {w : ℕ}

lemma bill_of_grade {a : ℕ → ℝ} {f : ℝ → ℝ} (H : Aspiration f a) (hv : ∀ j < w, a j = 0) :
    Bill w f := by
  obtain ⟨C,hc,h⟩ := (H.shift hv).bounded
  refine ⟨C,hc,?_⟩
  filter_upwards [h, eventually_pos] with r hr hr0
  have hr' : ‖r⁻¹ ^ w * f r‖ ≤ C := by simpa using hr
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ r⁻¹ ^ w), inv_pow] at hr'
  calc
    _ = (r⁻¹ ^ w * ‖f r‖)*r^w := by rw [mul_right_comm,inv_pow,inv_mul_cancel₀ (pow_pos hr0 _).ne',one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by rwa [inv_pow]) (pow_pos hr0 _).le

section vanishing
variable {Y : Fields G d → ℝ} (hv : d.SmoothAtFlat Y) (hy : RadialOrder w (Y ∘ d.tablePath))
    (t : d.Tags)
include R h hv hy

omit hv in
private lemma near_grade : RadialOrder w (nearFee P t Y) := by
  have he : ContDiffAt ℝ ∞ (fun x => Chart.jacobian P x * d.probability t (d.tablePath x)) 0 :=
    ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul (contDiffAt_const.congr_of_eventuallyEq
      (prob_flat_tangent (room_ok d h) t))
  intro x; simpa only [Nat.zero_add] using! bill_mul (directions he x).bounded (hy x)

private lemma bare_zeros {i : ℕ} (hi : i < w) (x : Coordinates G d) :
    integrandSeries (d.phase G t) (nearFee P t Y) i x = 0 := by
  unfold integrandSeries Zone.mul
  refine Finset.sum_eq_zero fun j hj => ?_
  have hh := Finset.mem_antidiagonal.mp hj
  rw [jets_vanish (near_smooth P R t Y (room_ok d h) hv) (near_grade P R h hy t) (show j.1 < w by omega)]; simp

lemma gaussian_grade {i : ℕ} (hi : i < w) : gaussianTerm P t Y i = 0 := by
  unfold gaussianTerm Radial.moment normTerm
  simp_rw [bare_zeros P R h hv hy t hi, zero_mul, integral_zero]

lemma gaussian_origin (x : Coordinates G d) : integrandSeries (d.phase G t) (nearFee P t Y) w x = jet (nearFee P t Y) w x := by
  unfold integrandSeries Zone.mul; rw [Finset.sum_eq_single (w,0)]
  · simp [expsum,Zone.TaylorPow]
  · intro a ha he
    rw [jets_vanish (near_smooth P R t _ (room_ok d h) hv) (near_grade P R h hy t) (show a.1 < w from ?_)]
    · simp
    have hv := Finset.mem_antidiagonal.mp ha; obtain ⟨a,b⟩:=a; dsimp only at *; simp at he; omega
  simp

lemma region_grade (hs : Envelope Y) : Bill w (region t Y univ) := bill_of_grade (expands P R t Y h hs hv)
  (fun _ hi => gaussian_grade P R h hv hy t hi)
end vanishing

-- true field test now; grade not an engineering power of a_m but a bare g exponent
abbrev grade {X : Type*} [NormedAddCommGroup X] (d : Descent n c) (g : Config G n → X) (w : ℕ) :=
    RadialOrder w (g ∘ d.fine 1 ∘ d.tablePath)

lemma even_test {Y : Fields G d → ℝ} (h : d.SmoothAtFlat Y) : RadialOrder 0 (Y ∘ d.tablePath) :=
  fun x => (directions h x).bounded

section shift
variable {g : Config G n → ℝ} (u : ℕ → ℝ) (hg : d.Testable g) (hG : d.grade g w)
    (t : d.Tags)
include h hg hG
omit hg in
private lemma reset_grade : RadialOrder w (d.resetTerms u g t ∘ d.tablePath) := by
  let f := g ∘ d.fine 1 ∘ d.tablePath
  let s (x : Coordinates G d) := Real.exp (- d.account u t 1 (d.tablePath x))
  have hs : ContDiffAt ℝ ∞ s 0 := ((account_smooth (room_ok d h) t u).of_le le_top).neg.exp
  intro x
  simpa only [Nat.zero_add] using! bill_mul (directions hs x).bounded (hG x)

include R
lemma field_rank_zero (i : ℕ) (hi : i < w) : bareRank P d u g i = 0 := by
  rw [bareRank, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => gaussian_grade P R h ?_ (reset_grade h u hG j) j hi
  exact (((account_smooth (room_ok d h) j u).of_le le_top).neg.exp).mul hg.smooth

lemma ranking_grade (j : ℕ) (hj : j < w) : ranking P d u g j = 0 := by
  simp only [ranking, divide, term, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero; intro i hi
  have he := Finset.mem_antidiagonal.mp hi
  rw [field_rank_zero P R h u hg hG _ (by omega), zero_mul]

lemma generation_grade : Bill w (generation d u g) := bill_of_grade (bare_comparison P R u h hg) (field_rank_zero P R h u hg hG)

/-- Uses the statement one has proved through each order `w+k` *before* shifting. -/
theorem rescaled_formula : Aspiration (fun a : ℝ => a⁻¹^w * d.conditioned (offset u a) g 1) (fun j => ranking P d u g (w+j)) :=
    (coefficient_formula P R u h hg).shift (ranking_grade P R h u hg hG)
end shift
end YM.RGComparison.Core16.Descent
