import YM.Integration.ActualNextLocalDatum
import YM.Integration.ActualLayerFineAction
import YM.Integration.FullQLocalSelectedRetunedLayerInput

/-!
The actual next datum receives the complete fine-action authentication for
the same retuned layer list and interpolated marked packet. All transport is
the literal equality of the old coarse side with the next fine side.
No new formal matching, width, price or rank-cap hypothesis is added.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNextRetunedFineAction
open Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {Gamma : Census V} {J : Request V}

private def castLayers {a b : Side} (h : a = b) (L : List (Piece G a)) :
    List (Piece G b) := h ▸ L

private def castColors {a b : Side} (h : a = b)
    (W : TestSpace J.tests → Bulk.Colors Gamma G a) :
    TestSpace J.tests → Bulk.Colors Gamma G b := h ▸ W

private def castPackets {a b : Side} (h : a = b)
    (P : MarkedPackets J.tests G a Gamma) :
    MarkedPackets J.tests G b Gamma := h ▸ P

private def castGraded {a b : Side} (h : a = b) {L : List (Piece G a)}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers L p order rankCap width budget) :
    GradedVacuumLayers (castLayers h L) p order rankCap width budget := by
  cases h
  exact H

private theorem castInput {a b : Side} (h : a = b)
    {W : TestSpace J.tests → Bulk.Colors Gamma G a}
    {P : MarkedPackets J.tests G a Gamma} (H : InputColors W P) :
    InputColors (castColors h W) (castPackets h P) := by
  cases h
  exact H

omit [Fintype V] in
private theorem castVacuum {a b : Side} (h : a = b)
    {W : TestSpace J.tests → Bulk.Colors Gamma G a} {L : List (Piece G a)}
    (H : ∀ x, (W x).vac = ActualGradedVacuum.restored L) :
    ∀ x, (castColors h W x).vac = ActualGradedVacuum.restored (castLayers h L) := by
  cases h
  exact H

variable (run : Run G) {A : NumericSchedule run.family J}
    {datum : LocalFormal.Datum run.family Gamma}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain run.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    {eta_w : ℝ} {I : FullPreparedInputAt F eta_w}
    {M : AnalyticOutput caps Y K F}

/-- The old retuned output list, transported only along its level equality. -/
def layers (M : AnalyticOutput caps Y K F) {m : ℕ} (hm : datum.level = m + 1) :
    List (Piece G (run.family.side (m + 1) datum.period)) :=
  castLayers (congrArg (fun i => run.family.side i datum.period) hm)
    (ActualRunRetunedVacuum.retunedLayers run M)

/-- Every marked slot is the same finite interpolated output packet. -/
def packets (S : Retained.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1) :
    MarkedPackets J.tests G (run.family.side (m + 1) datum.period) Gamma :=
  castPackets (congrArg (fun i => run.family.side i datum.period) hm)
    (ActualRunInterpolatedPackets.onRun run datum.cutoff datum.period
      datum.level S.output.model r)

/-- The common vacuum remains exactly the whole retuned list. -/
def colors (S : Retained.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1) :
    TestSpace J.tests → Bulk.Colors Gamma G
      (run.family.side (m + 1) datum.period) :=
  castColors (congrArg (fun i => run.family.side i datum.period) hm)
    (S.onRun_retuned_layer_colors r)

/-- The full input contract is preserved by that same side equality. -/
theorem input_colors (S : Retained.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1) :
    InputColors (colors run S r hm) (packets run S r hm) :=
  castInput (congrArg (fun i => run.family.side i datum.period) hm)
    (S.onRun_retuned_layer_input r)

/-- Authenticate the full coupling-ray action at the actual next datum.
Both full analytic extensions are supplied by the existing native-path
theorem; no equality at a single coupling is promoted to a germ identity. -/
theorem whole_action (S : Retained.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : datum.level = m + 1)
    (W : Bulk.Colors Gamma G (run.family.side (m + 1) datum.period))
    (x : Exterior.fieldDir G (run.family.side m datum.period) 1) :
    Nonempty (FineWholeAction J (ActualNextLocalDatum.descend datum hm W x)
      (colors run S r hm) (layers run M hm)) := by
  have hg := castGraded
    (congrArg (fun i => run.family.side i datum.period) hm)
    (ActualRunRetunedGraded.graded run M)
  have hv : ∀ y, (S.onRun_retuned_layer_colors r y).vac =
      ActualGradedVacuum.restored (ActualRunRetunedVacuum.retunedLayers run M) := by
    intro y
    rfl
  exact ActualLayerFineAction.whole_action run Gamma J
    (ActualNextLocalDatum.descend datum hm W x) hg
    (A.output_width_pos datum.level) (colors run S r hm) (packets run S r hm)
    (input_colors run S r hm)
    (castVacuum (congrArg (fun i => run.family.side i datum.period) hm) hv)

end YM.Integration.ActualNextRetunedFineAction
end
