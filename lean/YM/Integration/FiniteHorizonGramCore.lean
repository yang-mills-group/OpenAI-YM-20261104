import YM.OPE.Levy.Panel

/-!
# Actual finite-horizon Gram control in the same running frame

The finite probes below use the original unselected physical two-point function,
at separation `r • detectors`, with the same `J r` in both slots. Qualitative
leading convergence already gives a bounded inverse on these finite probe
coordinates. No fixed-physical-frame growth estimate is charged to a
perturbative remainder.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteHorizonGram
open Set Filter Function Spec Climb OPE OPE.Levy
open YM.Push.FiniteDetection.Free
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

abbrev ProbeIndex (C : Family G) (d : ℕ) :=
  Fin (Module.finrank ℂ ((Bel C.book).Field d))

def probeBasis (C : Family G) (d : ℕ) :=
  Module.finBasis ℂ ((Bel C.book).Field d)

/-- Fixed finite free coordinates, with no scale-dependent basis choice. -/
def freeProbes (C : Family G) (d : ℕ) :
    (Bel C.book).Field d →ₗ[ℂ] (ProbeIndex C d → ℂ) :=
  LinearMap.pi fun i =>
    (linear₂ ((Bel C.book).classMoment (Bel C.book) (fun _ : Fin 2 => d)
      detectors)).flip (probeBasis C d i)

/-- Physical output fields are tested against the actual `J r` probe fields. -/
def physicalProbes (d : ℕ) (U : ∀ d : ℕ, Spin.change S d) (r : ℝ) :
    S.Field d →ₗ[ℂ] (ProbeIndex C d → ℂ) :=
  LinearMap.pi fun i =>
    (linear₂ (S.classMoment S (fun _ : Fin 2 => d) (r • detectors))).flip
      (U d (probeBasis C d i))

def runningProbes (d : ℕ) (U : ∀ d : ℕ, Spin.change S d) (r : ℝ) :
    (Bel C.book).Field d →ₗ[ℂ] (ProbeIndex C d → ℂ) :=
  (physicalProbes d U r).comp (U d).toLinearMap

lemma runningProbes_apply (d : ℕ) (U : ∀ d : ℕ, Spin.change S d) (r : ℝ)
    (v : (Bel C.book).Field d) (i : ProbeIndex C d) :
    runningProbes d U r v i =
      pair d S (r • detectors) (U d v) (U d (probeBasis C d i)) := rfl

lemma freeProbes_injective (C : Family G) (d : ℕ) :
    Injective (freeProbes C d) := by
  intro u v huv
  have hz : freeProbes C d (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hc (i : ProbeIndex C d) :
      linear₂ ((Bel C.book).classMoment (Bel C.book) (fun _ : Fin 2 => d)
        detectors) (u - v) (probeBasis C d i) = 0 := congr_fun hz i
  have he : free2 (C := C) d (u - v) (reflect d (u - v)) = 0 := by
    change linear₂ ((Bel C.book).classMoment (Bel C.book) (fun _ : Fin 2 => d)
      detectors) (u - v) (reflect d (u - v)) = 0
    rw [← (probeBasis C d).sum_repr (reflect d (u - v)), map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, hc, smul_zero]
  have hzero : u - v = 0 := by
    by_contra hne
    have hp := free_positive (C := C) d (u - v) hne
    rw [he] at hp
    simp at hp
  exact sub_eq_zero.mp hzero

/-- The original discrete scaling supplier already gives the same finite-probe
conditioning, including every field below the chosen output horizon. -/
theorem scaling_price (F : Final C f S) (d : ℕ) (X : Climb.Scaling S)
    (H : Pert.FirstExtension F X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ k in atTop, ∀ v : (Bel C.book).Field d,
      ‖runningProbes d (X.U k) (X.r k) v‖ ≤ K * ‖v‖ ∧
      ‖v‖ ≤ K * ‖runningProbes d (X.U k) (X.r k) v‖ := by
  apply Measuring.priced _ (freeProbes_injective C d)
  intro v
  apply tendsto_pi_nhds.mpr
  intro i
  exact Levy.limits F d X H v (probeBasis C d i)

end YM.Integration.FiniteHorizonGram
