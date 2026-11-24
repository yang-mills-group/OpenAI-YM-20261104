import YM.IterationFour.Vacuum.Price
import YM.FullVolume.Cross

/-!
Exact whole-action accounting for a supplied vacuum Coin on the retained Run.
The full actual-beta path action includes its base, cubic, quartic and loop
parts. The rendered layer list uses its original power-minus-rank prefactors.
The explicit remainder retains the beta discrepancy, all residual regular
activity, and the logarithm of the unchanged covered gas. No Run-to-Plan
accessor, formal coefficient match, or smallness of this remainder is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunWholeAction

open Lattice Wilson RG MeasureTheory
open PhysicalNext.Repeat.Legato IterationFour.Vacuum IterationFour.Currency
open scoped BigOperators

variable {G : Gauge} (R : Run G) {N q r i : ℕ}
    (P : Plan R.family N q r) (U : Rep G (R.family.side i q))

/-- The full actual-beta path action and every rendered extra layer. -/
def renderedAction (V : Config G (R.family.side i q)) : ℝ :=
  (R.family.path.rep N q i).path.inChannels U.clip U.p
      (R.family.path.β N q i) V +
    Render.renders (Render.prefactor (g R.family N q i)) U.p V (P.layers i)

/-- The original beta discrepancy and all residual regular activity. -/
def exponentResidual (V : Config G (R.family.side i q)) : ℝ :=
  (U.beta - R.family.path.β N q i) *
      Push.BetaTransport.kinetic U.path U.clip U.p V +
    U.activities.additive U.p V

/-- Full density residual: the covered gas is retained, with its original K. -/
def densityResidual (V : Config G (R.family.side i q)) : ℝ :=
  exponentResidual R (N := N) U V - Real.log (U.activities.gas U.p V)

/-- Remove only the literal flat scalar of the same retained history. -/
def actualAction (V : Config G (R.family.side i q)) : ℝ :=
  (R.family.path.rep N q i).scalar -
    Real.log ((R.family.path.rep N q i).eval V)

/-- The leading base/cubic/quartic contribution and the original loop action
are both present before the additional layers are rendered. -/
theorem renderedAction_split (V : Config G (R.family.side i q)) :
    renderedAction R P U V =
      R.family.path.β N q i *
          Push.BetaTransport.kinetic (R.family.path.rep N q i).path U.clip U.p V +
        (R.family.path.rep N q i).path.inChannels U.clip U.p 0 V +
        Render.renders (Render.prefactor (g R.family N q i)) U.p V (P.layers i) := by
  unfold renderedAction
  rw [Push.BetaTransport.channels_split V (R.family.path.β N q i)]

/-- Appending the model leaves every original covered-gas coefficient intact. -/
theorem gas_preserved (V : Config G (R.family.side i q)) :
    (loaded R.family N q i (P.layers i) U).activities.gas
        (loaded R.family N q i (P.layers i) U).p V = U.activities.gas U.p V := by
  exact congrFun (Render.gas (Render.prefactor (g R.family N q i))
    U.activities (P.layers i) U.p) V

variable {x γ l : ℝ}
    (h : Coin R.family N q i (P.layers i) U x γ l) (hi : i ≤ N)

include h hi

/-- Pointwise exact exponent identity; no residual term is discarded. -/
theorem whole_exponent (V : Config G (R.family.side i q)) :
    (loaded R.family N q i (P.layers i) U).exponent V =
      (R.family.path.rep N q i).scalar - renderedAction R P U V -
        exponentResidual R (N := N) U V := by
  rw [h.read_exponent R.makes hi V]
  have hp : Render.permits (P.layers i) U.p := by
    rw [h.types.budget]
    exact h.lives
  have hu : U.activities.Valid U.p x γ := by
    rw [h.types.budget]
    exact h.error
  have ha : (loaded R.family N q i (P.layers i) U).activities.additive U.p V =
      U.activities.additive U.p V +
        Render.renders (Render.prefactor (g R.family N q i)) U.p V (P.layers i) :=
    Render.additive (Render.prefactor (g R.family N q i)) hp hu V
  rw [ha]
  unfold renderedAction exponentResidual
  ring

/-- Exact retained density, before any logarithm or normalization. -/
theorem whole_density (V : Config G (R.family.side i q)) :
    (R.family.path.rep N q i).eval V =
      Real.exp ((R.family.path.rep N q i).scalar - renderedAction R P U V -
        exponentResidual R (N := N) U V) * U.activities.gas U.p V := by
  rw [← congrFun h.value V, Rep.eval, whole_exponent R P U h hi V]
  rw [gas_preserved R P U V]

/-- Positivity comes from this Coin's equality to the original physical density. -/
theorem covered_gas_pos (V : Config G (R.family.side i q)) :
    0 < U.activities.gas U.p V := by
  have hv := h.positive R.makes hi V
  rw [h.value, whole_density R P U h hi V] at hv
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hv

/-- The strongest exact whole-action match supplied by Coin alone. -/
theorem whole_action (V : Config G (R.family.side i q)) :
    actualAction R (N := N) V = renderedAction R P U V + densityResidual R (N := N) U V := by
  unfold actualAction densityResidual
  rw [whole_density R P U h hi V,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (covered_gas_pos R P U h hi V)),
    Real.log_exp]
  ring

/-- The same full expression integrates to the original fine-level partition. -/
theorem original_partition :
    (∫ V, Real.exp ((R.family.path.rep N q i).scalar - renderedAction R P U V -
        exponentResidual R (N := N) U V) * U.activities.gas U.p V ∂prior G _) =
      partition G (R.family.side N q) (R.family.beta N q) := by
  have he : (fun V => Real.exp ((R.family.path.rep N q i).scalar -
      renderedAction R P U V - exponentResidual R (N := N) U V) * U.activities.gas U.p V) =
      (loaded R.family N q i (P.layers i) U).eval := by
    funext V
    rw [h.value, whole_density R P U h hi V]
  rw [he]
  exact h.paid_partition R.makes hi

end YM.Integration.ActualRunWholeAction
