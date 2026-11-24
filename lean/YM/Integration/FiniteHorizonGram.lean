import YM.Integration.FiniteHorizonGramCore
import YM.PhysMS.Frame.Measured

/-! Actual all-length finite-probe prices in the same leading frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FiniteHorizonGram
open Set Filter Function Spec Climb PhysMS OPE OPE.Levy Trace.Pilot
open YM.Push.FiniteDetection.Free
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

variable (F : Final C f S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J)

include H in
lemma runningProbes_tendsto (v : (Bel C.book).Field d) :
    Tendsto (fun r => runningProbes d (J r) r v) trail (𝓝 (freeProbes C d v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := leading_at F H (d := fun _ : Fin 2 => d) ![v, probeBasis C d i]
    tendsto_id (tendsto_const_nhds (x := detectors)) detectors_in
  convert h using 1 <;> congr 1
  funext r
  apply DFunLike.congr_arg (S.classMoment S (fun _ : Fin 2 => d) (r • detectors))
  funext j
  fin_cases j <;> rfl

include H in
/-- The full finite output horizon has one eventual two-sided constant. -/
theorem running_price : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail,
    ∀ v : (Bel C.book).Field d,
      ‖runningProbes d (J r) r v‖ ≤ K * ‖v‖ ∧
      ‖v‖ ≤ K * ‖runningProbes d (J r) r v‖ :=
  Measuring.priced (runningProbes_tendsto F d J H) (freeProbes_injective C d)

include H in
/-- An inverse bound on actual physical outputs, expressed in the same `J r`
coordinates. The physical separation and the probe fields remain explicit. -/
theorem physical_price : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail,
    ∀ v : S.Field d,
      ‖physicalProbes d (J r) r v‖ ≤ K * ‖(J r d).symm v‖ ∧
      ‖(J r d).symm v‖ ≤ K * ‖physicalProbes d (J r) r v‖ := by
  obtain ⟨K, hK, hp⟩ := running_price F d J H
  refine ⟨K, hK, hp.mono fun r hr v => ?_⟩
  simpa only [runningProbes, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hr ((J r d).symm v)

include H in
/-- Finite probe errors control a candidate coefficient vector with no extra
power of the physical scale. This is the core OPE use of the inverse bound. -/
theorem coefficient_error : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail,
    ∀ (v : S.Field d) (w : (Bel C.book).Field d),
      ‖(J r d).symm v - w‖ ≤
        K * ‖physicalProbes d (J r) r v - runningProbes d (J r) r w‖ := by
  obtain ⟨K, hK, hp⟩ := running_price F d J H
  refine ⟨K, hK, hp.mono fun r hr v w => ?_⟩
  simpa only [map_sub, runningProbes, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (hr ((J r d).symm v - w)).2

end YM.Integration.FiniteHorizonGram
