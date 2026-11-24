import YM.Integration.WilsonEmittedCutGrouping

/-! The genuine unmasked group operand needs only its own two original
paths from the marked address. Thus a cut at a small fraction of B fits
inside the prescribed B-cube on the original cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWordFootprint
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.Density.Mirrors WilsonEmittedCutGrouping
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (s : Γ.Mode) (m : ℕ) (v : V) (hv : v∈s.val)
include hv

theorem inside {i : ι} (hi : early M s m i) :
    (M i).atom.footprint (M i).center ⊆ neighborhood (2*m) (P.origin v) := by
  intro x hx
  have hd : v ∈ (M i).mode.val := hi.1 ▸ hv
  have hp := (M i).binder.covers (M i).atom v hd (P.born v)
  have lc := (M i).binder.spread (M i).atom hp
  have xc := (M i).binder.spread (M i).atom ((M i).binder.footprint (M i).atom hx)
  rw [separation_comm] at lc
  apply (neighborhood_iff ..).2
  have tri := separation_triangle (P.origin v) (M i).center x
  have hl := hi.2
  change separation (P.origin v) (M i).center≤(M i).length at lc
  change separation (M i).center x≤(M i).length at xc
  omega

theorem kept (q : ι → ℂ) (B : BudgetPoint) (g : ℝ) {k : ℕ} (h : 2*m≤k) :
    LocalOn (neighborhood k (P.origin v)) (Air.sums M q (early M s m) g) := by
  intro U W hw
  apply tsum_congr
  intro i
  by_cases hi : early M s m i
  · have land := (inside M s m v hv hi).trans (neighborhood_mono h)
    obtain ⟨atSite,-⟩ := Extra.Iteration.Derivs.canonical_regular (M i).atom (M i).center B (M i).lawful
    have actual := atSite U W (agrees_mono hw land)
    simp only [if_pos hi,ScatterR.familyAt,Sunrise.Loan.letter,actual]
  · simp [hi]

end YM.Integration.WilsonEmittedWordFootprint
