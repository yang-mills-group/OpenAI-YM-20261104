import YM.Integration.MSPhysicalDeckChange
import YM.Integration.MSNormalizedFeeReadout
import YM.Integration.MSMeasuredGermSeries

/-! The field measured by a true marked prescription. A rectangular
cutoff-germ solve kills every smaller engineering component at all orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMeasuredFeeField

open Filter FVA2 MS MS.Local.Physical MS.Land MS.Menus MSPhysicalDeckChange
open MSFeeCoordinates MSCutoffGerms MSMeasuredGermSeries
open scoped Classical Topology BigOperators

variable {G : Gauge} {A B : Deck G} (P : Prescription A) (E : Fees B A) {h d : ℕ}
variable {I : Type*} {l : Filter I} {t : I → ℝ}

def raw (b : Glyph B h) (a : Glyph A d) : MSFeeCoordinates.R :=
  if ha : a.size ≤ b.size then receiver P (E b.size b.2) (restrict a ha) else 0

theorem above (b : Glyph B h) (a : Glyph A d) (ha : b.size < a.size) :
    raw P E b a = 0 := by rw [raw, dif_neg (not_le.mpr ha)]

theorem pad {h' d' : ℕ} (p : h ≤ h') (q : d ≤ d') (b : Glyph B h) (a : Glyph A d) :
    raw P E (MSFeeCoordinates.extend p b) (MSFeeCoordinates.extend q a) = raw P E b a := rfl

def charged (μ θ : ℝ) (b : Glyph B h) (a : Glyph A d) : PowerSeries ℂ :=
  PowerSeries.C (Port.τ ((b.size : ℤ) - a.size) θ) *
    MSNormalizedFeeReadout.into (evaluate (μ-θ) (raw P E b a))

theorem rate (μ θ : ℝ) (b : Glyph B h) (a : Glyph A d) (k : ℕ) :
    PowerSeries.coeff k (charged P E μ θ b a) =
      ((Real.exp (((b.size : ℝ)-a.size)*θ) *
        (PowerSeries.coeff k (raw P E b a)).eval (μ-θ) : ℝ) : ℂ) := by
  rw [charged, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, evaluate, PowerSeries.coeff_map,
    Complex.ofReal_mul]
  congr 1
  unfold Port.τ
  apply congrArg Complex.ofReal
  simp only [zpow_sub₀ (Real.exp_ne_zero θ), zpow_natCast, sub_mul, Real.exp_sub, Real.exp_nat_mul]

theorem same_grade (μ : ℝ) (b : Glyph B h) (a : Glyph A d)
    (u : ℝ) (v : ℕ) (hw : b.size = a.size) :
    PowerSeries.coeff v (charged P E μ u b a) =
      ((PowerSeries.coeff v (raw P E b a)).eval (μ-u) : ℝ) := by
  rw [rate, hw]
  simp

theorem extinguish [NeBot l] (ht : Tendsto t l atTop) (μ : ℝ) (b : Glyph B h) (a : Glyph A d)
    (ha : a.size < b.size) (f : PowerSeries (ring ht))
    (hs : diagram l (fun i => charged P E μ (t i) b a) =
      PowerSeries.map (ring ht).subtype f) :
    raw P E b a = 0 := by
  apply PowerSeries.ext
  intro k
  rw [map_zero]
  have hg : hom l (fun i => PowerSeries.coeff k (charged P E μ (t i) b a)) ∈ ring ht := by
    rw [← coefficient, hs, PowerSeries.coeff_map]
    exact (PowerSeries.coeff k f).property
  have hsub := (member ht _).mp hg
  simp only [rate] at hsub
  exact no_lower ht μ ((b.size : ℝ)-a.size)
    (sub_pos.mpr (by exact_mod_cast ha)) _ hsub

end YM.Integration.MSMeasuredFeeField
