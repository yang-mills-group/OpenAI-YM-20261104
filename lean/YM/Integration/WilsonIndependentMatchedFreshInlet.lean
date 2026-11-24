import YM.Integration.WilsonIndependentMatchedSectionIncome
import YM.RG06.Wilson.Inlet

/-! The slot-normalized angular symbol of the registered compact Wilson section
itself on the elected run.  The same finite detector wallet sees every radial
row, including the embedded lower polynomial and the unit at a larger cap. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshInlet
open RG06.GSeries Function Gauge Exterior Source Source.Drops PertExtension.Heat Lattice RG Bid Wilson Labels
open PhysicalNext.Repeat.Legato
open RG06 RG06.WilsonCompiler Push.CutoffProjectors
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} (R : Run G) {d : ℕ}

def symbol (i : (R.family.labels.level d).Index) (v : Lens G d) : ℂ :=
  iteratedDeriv (v.2 : ℕ) (fun r : ℝ => tone (input v.1 d r)
    (PowerSeries.constantCoeff (voice (((R.family.labels.level d).grades i).2)
      (markTop R.family d (Pi.single i 1))))) 0

theorem registered (i : (R.family.labels.level d).Index) (v : Lens G d) :
    symbol R i v = probe (R.family.labels.level d) v (Pi.single i 1) := by
  rw [probe_eq, ← (R.family.labels.level d).coords_basis i, LinearEquiv.symm_apply_apply]
  exact reads_inlet R.family R.makes (FVAAlt2.Block.clothes R d) i v.1 v.2 (by omega)

def bank (d : ℕ) (x : (R.family.labels.level d).Coeff) (v : Lens G d) : ℂ :=
  ∑ i, x i * symbol R i v

theorem earned (x : (R.family.labels.level d).Coeff) (v : Lens G d) :
    bank R d x v = probe (R.family.labels.level d) v x := by
  classical
  have hw : (∑ i, x i • (Pi.single i (1 : ℂ) : (R.family.labels.level d).Coeff)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    _ = probe (R.family.labels.level d) v
        (∑ i, x i • (Pi.single i (1 : ℂ) : (R.family.labels.level d).Coeff)) := by
      simp only [bank, registered, map_sum, map_smul, smul_eq_mul]
    _ = _ := congrArg _ hw

theorem original (d : ℕ) :
    ∃ (tests : Finset (Lens G d)) (c : ℝ), 0 < c ∧
      ∀ x : (R.family.labels.level d).Coeff,
        c * ‖x‖ ≤ ∑ t ∈ tests, ‖bank R d x t‖ := by
  simpa only [earned] using probes_bound (R.family.labels.level d)

def embed {d e : ℕ} (h : d ≤ e) (x : (R.family.labels.level d).Coeff) :
    (R.family.labels.level e).Coeff :=
  (R.family.labels.level e).coords (raiseLabel G h ((R.family.labels.level d).coords.symm x))

theorem lifted {e : ℕ} (h : d ≤ e) (x : (R.family.labels.level d).Coeff) (J : Jet G)
    (n : ℕ) (order : n ≤ d) :
    bank R e (embed R h x) (J, ⟨n, by omega⟩) = bank R d x (J, ⟨n, by omega⟩) := by
  simp only [earned, probe_eq, embed, LinearEquiv.symm_apply_apply]
  rfl

theorem unit (d : ℕ) (v : Lens G d) :
    bank R d (R.family.labels.level d).e0 v = iteratedDeriv (v.2 : ℕ) (fun _ : ℝ => (1:ℂ)) 0 := by
  rw [earned, probe_eq, ← (R.family.labels.level d).coords_unit, LinearEquiv.symm_apply_apply]
  simp only [Labels.unit, map_one]

end YM.Integration.WilsonIndependentMatchedFreshInlet
