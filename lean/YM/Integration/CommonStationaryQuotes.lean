import YM.Push.STATIONARY_UNIFORM.Cost

/-! A stationary quote selected from finite stage parameters before any
block size, period, path or Run. Its exact polynomial bill is available to
an initial request constructor. This file neither purchases that bill nor
asserts a bound along an already selected changing-stage trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CommonStationaryQuotes
open Lattice Wilson RG Push.Uniform

/-- The identical choice expression used by ActualSpringStationaryService,
with its finite parameters exposed instead of extracted from a Run. -/
def quote (G : Gauge) (μ C : ℝ) (j : ℕ) (Q : KernelChoices) (n : ℕ) :
    Before G μ C j Q (n + 3) :=
  Classical.choice (pre_order G μ C j Q (by omega))

/-- One positive bill containing the Hessian value/inverse prices and
all inverse radii/rates used by the stationary chart. -/
def bill (T : ChartPrices) : ℝ :=
  1 + T.value + T.inverse + T.gap⁻¹ + T.width⁻¹ + T.rate⁻¹ +
    T.initial⁻¹ + T.safety⁻¹ + T.zone⁻¹ + T.horizon⁻¹

variable (G : Gauge) (μ C : ℝ) (j : ℕ) (Q : KernelChoices) (n : ℕ)
    (hμ : 0 < μ) (p : Clip)
include hμ

theorem bill_ge_one (P : Patch) (hP : P.J = j) :
    1 ≤ bill ((quote G μ C j Q n).tables p P) := by
  obtain ⟨hv, hw, hr, hi, hg, hs, hI, hz, hh⟩ :=
    Before.power G (quote G μ C j Q n) hμ p
  have h1 := (hv.pos P hP).le
  have h2 := (hI.pos P hP).le
  have h3 := (inv_pos.mpr (hg.pos P hP)).le
  have h4 := (inv_pos.mpr (hw.pos P hP)).le
  have h5 := (inv_pos.mpr (hr.pos P hP)).le
  have h6 := (inv_pos.mpr (hi.pos P hP)).le
  have h7 := (inv_pos.mpr (hs.pos P hP)).le
  have h8 := (inv_pos.mpr (hz.pos P hP)).le
  have h9 := (inv_pos.mpr (hh.pos P hP)).le
  dsimp only [bill]
  linarith

/-- Fixed stage and requested derivative order, uniformly over every
later Patch with that stage. No torus or forest is an input. -/
theorem bill_tame :
    Tame j (fun P => bill ((quote G μ C j Q n).tables p P)) := by
  obtain ⟨hv, hw, hr, hi, hg, hs, hI, hz, hh⟩ :=
    Before.power G (quote G μ C j Q n) hμ p
  exact (((((((((tame_k (j := j) 1).add hv.high).add hI.high).add hg.low).add
    hw.low).add hr.low).add hi.low).add hs.low).add hz.low).add hh.low

/-- The exponent and constant are fixed before the later block size.
An initial requested-Delta adapter may purchase this exact displayed bill. -/
theorem bill_bound :
    ∃ (e : ℕ) (B : ℝ), 0 < B ∧ ∀ P : Patch, P.J = j →
      bill ((quote G μ C j Q n).tables p P) ≤ B * (P.L.val : ℝ) ^ e := by
  obtain ⟨e, B, hB, hb⟩ := bill_tame G μ C j Q n hμ p
  exact ⟨e, B, hB, fun P hP => (le_abs_self _).trans (hb P hP)⟩

end YM.Integration.CommonStationaryQuotes
