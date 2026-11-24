import YM.Integration.OPEPreparation
import YM.FullVolume.Cross
import Mathlib.RingTheory.PowerSeries.Substitution

/-! Transparent data for the coefficient-identification boundary. Every
source term retains its original Family, horizon, basis label and position.
Finite formal-series mixtures are formed before one common coupling reset.
This file supplies the actual RG10 coefficient formula and normalization;
it does not assert agreement with an MS prescription or a physical expansion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CoefficientBridge
open Lattice Wilson PowerSeries RG06
open FormalOPE.RG10 FormalOPE.RG10.InversionTop
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

/-- All choices are explicit data, fixed before a coefficient order or a
subset of insertions is queried. Each term uses its own original horizon. -/
structure Preparation {G : Gauge} (C : Family G) (I W : Type) where
  cutoff : I → ℕ
  period : I → ℕ
  terms : W → ℕ
  degree : (w : W) → Fin (terms w) → ℕ
  basis : (w : W) → (j : Fin (terms w)) →
    (C.labels.level (degree w j)).Index
  position : (i : I) → (w : W) → Fin (terms w) →
    Site (C.side (cutoff i) (period i))
  weight : (i : I) → (w : W) → Fin (terms w) → Series
  ratio : I → PowerSeries ℝ

namespace Preparation
variable {G : Gauge} {C : Family G} {I W : Type} (D : Preparation C I W)

theorem even (i : I) : Even (C.side (D.cutoff i) (D.period i)).val := by
  obtain ⟨q, hq⟩ := C.S.side_four (D.cutoff i) (D.period i)
  change (C.side (D.cutoff i) (D.period i)).val = 4 * q at hq
  exact ⟨2 * q, by omega⟩

/-- The exact real ratio is embedded into the same complex coefficient ring.
The reset has zero constant term for every ratio, so substitution is formal
and legitimate without an analytic convergence assumption. -/
def reset (i : I) : Series :=
  PowerSeries.X * PowerSeries.map Complex.ofRealHom (D.ratio i)

def resetHom (i : I) : Series →ₐ[ℂ] Series :=
  PowerSeries.substAlgHom (a := D.reset i) (PowerSeries.HasSubst.of_constantCoeff_zero'
    (by simp [reset]))

def factors (i : I) :
    W → Kernel (Unit × PertExtension.Orb.Dir G (C.side (D.cutoff i) (D.period i))) :=
  preparedOPEFactors C (D.cutoff i) (D.period i)
    D.degree (D.position i) D.basis (D.weight i)

/-- Ordinary normalized inversion-regulator series, before common reset. -/
def raw (i : I) (s : Finset W) : Series :=
  (InversionTop.feed (D.even i)).ordinary
    (InversionTop.vertices G (C.side (D.cutoff i) (D.period i))) s (D.factors i)

/-- The full series is reset once; individual slots never use independent
coupling variables or independently selected resets. -/
def series (i : I) (s : Finset W) : Series := D.resetHom i (D.raw i s)

def coefficients (s : Finset W) (k : ℕ) (i : I) : ℂ :=
  PowerSeries.coeff k (D.series i s)

@[simp] theorem raw_empty (i : I) : D.raw i ∅ = 1 := by
  simp [raw, FlatFeed.ordinary]

@[simp] theorem series_empty (i : I) : D.series i ∅ = 1 := by
  rw [series, raw_empty, map_one]

@[simp] theorem coefficients_empty (k : ℕ) (i : I) :
    D.coefficients ∅ k i = if k = 0 then 1 else 0 := by
  simp only [coefficients, series_empty, PowerSeries.coeff_one]

/-- The integrals defining every finite marked coefficient genuinely exist.
This is supplied by the original section valuation, not by identification. -/
theorem funded (hC : C.Makes) (hV : ∀ d, Bid.pop (C.localSection d))
    (i : I) (s : Finset W) :
    (InversionTop.feed (D.even i)).Funded
      ((InversionTop.vertices G (C.side (D.cutoff i) (D.period i))).weight *
        ∏ w ∈ s, D.factors i w) := by
  exact (preparedOPE_subsets C (D.cutoff i) (D.period i) hC hV
    D.degree (D.position i) D.basis (D.weight i) (D.even i) s).1

end Preparation

/-- Valuation is already present on the retained common Run. -/
theorem run_valuation {G : Gauge} (R : Run G) (d : ℕ) :
    Bid.pop (R.family.localSection d) := Next.Foundations.valuation G d

/-- No extra physical or analytic premise is needed to make the coefficient
formula well-defined on the common construction. -/
theorem run_funded {G : Gauge} (R : Run G) {I W : Type}
    (D : Preparation R.family I W) (i : I) (s : Finset W) :
    (InversionTop.feed (D.even i)).Funded
      ((InversionTop.vertices G (R.family.side (D.cutoff i) (D.period i))).weight *
        ∏ w ∈ s, D.factors i w) :=
  D.funded R.makes (run_valuation R) i s

end YM.Integration.CoefficientBridge
