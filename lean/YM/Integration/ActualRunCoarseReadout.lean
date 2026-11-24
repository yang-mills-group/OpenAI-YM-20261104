import YM.Integration.ActualCoveredNormalization
import YM.Integration.ActualRunWholeAction
import YM.Push.GRID_APPROXIMATION.Iterate

/-!
Exact normalized readout on the original full coarse configuration space.
Every level uses the same original fine Wilson partition. The action formula
retains the beta discrepancy, regular remainder and full covered gas.
This file makes no inversion-quotient or MS identification and no estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunCoarseReadout
open MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato
open IterationFour.Vacuum IterationFour.Currency
open scoped BigOperators

variable {G : Gauge} (R : Run G)

/-- A full unnormalized density is read against coarse product Haar and the
original fine partition. Use with an integrable density. -/
def readout (N p m : ℕ) (F : Config G (R.family.side m p) → ℂ) : ℂ :=
  (partition G (R.family.side N p) (R.family.beta N p) : ℂ)⁻¹ *
    ∫ U, F U ∂prior G (R.family.side m p)

/-- The actual coarse density occurs once, before normalization. -/
def expectation (N p m : ℕ) (F : Config G (R.family.side m p) → ℂ) : ℂ :=
  readout R N p m (fun U => ((R.family.path.rep N p m).eval U : ℂ) * F U)

theorem vacuum_one (N p m : ℕ) (hm : m ≤ N) :
    expectation R N p m (fun _ => 1) = 1 := by
  unfold expectation readout
  simp only [mul_one]
  rw [integral_complex_ofReal,
    (ActualCoveredNormalization.same_run_reference R N p m hm).2.2]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')

/-- One actual blocking step preserves the entire signed numerator. -/
theorem push_readout (N p m : ℕ)
    (F : Config G (R.family.side (m + 1) p) → ℂ)
    (hF : Integrable F (prior G (R.family.side (m + 1) p))) :
    readout R N p m
        ((R.family.path.levels.clock.op m p).push
          (R.family.path.β N p (m + 1)) F) =
      readout R N p (m + 1) F := by
  unfold readout
  rw [StepData.push_integral (R.family.path.levels.transition_mass ..) F hF]

/-- At the fine endpoint this is the original Wilson law, with its actual beta. -/
theorem original_readout (N p : ℕ)
    (F : Config G (R.family.side N p) → ℂ)
    (hF : Integrable F (law G (R.family.side N p) (R.family.beta N p))) :
    expectation R N p N F = R.family.omega N p F := by
  unfold expectation readout Family.omega
  have hb : (R.family.path.rep N p N).eval = bare (R.family.beta N p) :=
    (R.makes.wilson.starts N p).2
  rw [hb]
  exact (moment_formula _ _ hF).symm

/-- The actual full density obtained by the original iterated blocking map. -/
def pushedDensity (N p m : ℕ) (hm : m ≤ N)
    (F : Config G (R.family.side N p) → ℂ) :
    Config G (R.family.side m p) → ℂ :=
  Push.GridApprox.pushTo R.family.path N p hm
    (fun U => (bare (R.family.beta N p) U : ℂ) * F U)

/-- The native iterated full push preserves the original normalized Wilson
readout. No replacement density or recurrence is supplied by the caller. -/
theorem original_to_coarse (N p m : ℕ) (hm : m ≤ N)
    (F : Config G (R.family.side N p) → ℂ)
    (hF : Integrable F (law G (R.family.side N p) (R.family.beta N p))) :
    Integrable (pushedDensity R N p m hm F) (prior G (R.family.side m p)) ∧
      readout R N p m (pushedDensity R N p m hm F) = R.family.omega N p F := by
  have h := hF
  rw [law, integrable_withDensity_iff_integrable_smul'
    (weight_meas _) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h
  have hw : Integrable (fun U : Config G (R.family.side N p) =>
      (bare (R.family.beta N p) U : ℂ) * F U) (prior G (R.family.side N p)) := by
    convert h.const_mul (partition G (R.family.side N p) (R.family.beta N p) : ℂ) using 1
    funext U
    rw [Wilson.weight, ENNReal.toReal_ofReal
      (div_pos (bare_pos _ _) (partition_pos _)).le,
      Complex.real_smul, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr (partition_pos (R.family.beta N p)).ne']
  refine ⟨Push.GridApprox.pushTo_integrable R.family.path N p hm _ hw, ?_⟩
  unfold readout pushedDensity Family.omega
  rw [Push.GridApprox.pushTo_integral R.family.path N p hm _ hw]
  exact (moment_formula _ _ hF).symm

/-- The complete Coin action is retained inside the same coarse integral.
In particular neither the residual regular action nor the covered gas is
replaced by one. This is an equality of readouts, not a new integrability claim. -/
theorem whole_action_readout {N p r m : ℕ}
    (P : Plan R.family N p r) (U : Rep G (R.family.side m p))
    {x γ l : ℝ} (h : Coin R.family N p m (P.layers m) U x γ l)
    (hm : m ≤ N) (F : Config G (R.family.side m p) → ℂ) :
    expectation R N p m F =
      readout R N p m (fun V =>
        ((Real.exp ((R.family.path.rep N p m).scalar -
            ActualRunWholeAction.renderedAction R P U V -
            ActualRunWholeAction.exponentResidual R (N := N) U V) *
          U.activities.gas U.p V : ℝ) : ℂ) * F V) := by
  unfold expectation
  congr 1
  funext V
  rw [ActualRunWholeAction.whole_density R P U h hm V]

end YM.Integration.ActualRunCoarseReadout
