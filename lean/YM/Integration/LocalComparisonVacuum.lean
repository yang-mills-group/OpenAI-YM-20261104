import YM.IterationFour.Vacuum.Trace

/-!
Native vacuum portion of the external local-comparison contract.

`vacuumRate` is the pre-reset estimate: inherited smooth error receives the
contraction factor, while calibration receives only the geometric price.
The error is represented by `Coin` and `Local` inside `Early`; it is not an
analytic coupling vertex. The incoming and outgoing expressions use the
specified actual Family, cutoff, period, level, and full loaded vacuum.

This file does not identify `Plan.layers` or `Plan.coefficient` with the
independently defined complete Fk prescription. That literal binding remains
an external obligation. The history adapter below is conditional on the
original `Counter`, `Room`, and rigidity receipts; it supplies no missing
local estimate or repeated-use admission.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

open Lattice Wilson RG
open IterationFour IterationFour.Vacuum
open scoped BigOperators Classical

variable {G : Gauge}

/-- The pre-reset regular vacuum rate. -/
def vacuumRate (order : ℕ)
    (constant block vanishing geometry inherited calibration coupling : ℝ) : ℝ :=
  (constant / block + vanishing) * inherited +
    coupling ^ (order + 1) * geometry + geometry * calibration

/-- A native scalar bill for precisely the three terms of the vacuum rate.
Positivity is explicit; no bound on an unknown error is inferred here. -/
def vacuumPocket (order : ℕ)
    (constant block vanishing geometry coupling forceEarly forceGoal : ℝ)
    (hRepeat : 0 ≤ constant / block + vanishing)
    (hTaylor : 0 ≤ coupling ^ (order + 1) * geometry)
    (hGeometry : 0 ≤ geometry) : Pocket where
  repeatCost := constant / block + vanishing
  taylor := coupling ^ (order + 1) * geometry
  transport := 0
  response := geometry
  outside := 0
  forceEarly := forceEarly
  forceGoal := forceGoal
  prices_pos := ⟨hRepeat, hTaylor, le_rfl, hGeometry, le_rfl⟩

theorem vacuumPocket_due (order : ℕ)
    (constant block vanishing geometry coupling forceEarly forceGoal : ℝ)
    (hRepeat : 0 ≤ constant / block + vanishing)
    (hTaylor : 0 ≤ coupling ^ (order + 1) * geometry)
    (hGeometry : 0 ≤ geometry) (inherited calibration : ℝ) :
    (vacuumPocket order constant block vanishing geometry coupling
      forceEarly forceGoal hRepeat hTaylor hGeometry).due inherited calibration =
      vacuumRate order constant block vanishing geometry inherited calibration coupling := by
  simp only [vacuumPocket, Pocket.due, Pocket.single, vacuumRate, add_zero]

/-- The one-step vacuum estimate that the external supplier must produce.
`Early` is before affine reclosure; `resume` later charges `owed`, not merely
this pre-reset rate. The displayed incoming beta may differ from the actual
kernel beta by the explicitly retained `mismatchIn` amount. -/
structure VacuumLocalClause {C : Family G} {N period order : ℕ}
    (P : Plan C N period order) (level : ℕ)
    (incoming : Rep G (C.side (level + 1) period))
    (inherited forcedIn mismatchIn constant vanishing geometry calibration
      forcedEarly : ℝ) : Prop where
  order_ge_two : 2 ≤ order
  step : level < N
  input : Coin C N period (level + 1) (P.layers (level + 1)) incoming
    inherited forcedIn mismatchIn
  early : ∃ X v τ,
    Early C N period level (P.layers level) X v τ
      (P.predict level) (P.alpha level)
      (vacuumRate order constant (C.S.block level).val vanishing geometry
        inherited calibration (Currency.g C N period (level + 1)))
      forcedEarly
      (advance C N period level (P.layers (level + 1)) incoming)

/-- The full pushed input is exactly the already specified actual coarse
vacuum. This uses `Coin.value`, including the loaded model and residual. -/
theorem vacuum_advance_eq_actual {C : Family G} (hC : C.Makes)
    {N period level : ℕ} (hLevel : level < N)
    {layers : List (Piece G (C.side (level + 1) period))}
    {incoming : Rep G (C.side (level + 1) period)}
    {inherited forced mismatch : ℝ}
    (hInput : Coin C N period (level + 1) layers incoming inherited forced mismatch) :
    advance C N period level layers incoming = (C.path.rep N period level).eval := by
  rw [advance, hInput.value]
  exact (hC.wilson.steps N period level hLevel).1.symm

/-- The external local clause can be consumed at the actual coarse vacuum,
without strengthening the displayed-beta mismatch to an equality. -/
theorem VacuumLocalClause.at_actual {C : Family G} {N period order : ℕ}
    {P : Plan C N period order} {level : ℕ}
    {incoming : Rep G (C.side (level + 1) period)}
    {inherited forcedIn mismatchIn constant vanishing geometry calibration forcedEarly : ℝ}
    (h : VacuumLocalClause P level incoming inherited forcedIn mismatchIn
      constant vanishing geometry calibration forcedEarly) (hC : C.Makes) :
    ∃ X v τ, Early C N period level (P.layers level) X v τ
      (P.predict level) (P.alpha level)
      (vacuumRate order constant (C.S.block level).val vanishing geometry
        inherited calibration (Currency.g C N period (level + 1)))
      forcedEarly (C.path.rep N period level).eval := by
  simpa only [vacuum_advance_eq_actual hC h.step h.input] using h.early

/-- Existing conditional induction, with its actual-law and beta readings
made explicit for consumers. `Counter` contains the genuine local estimates;
`Room` retains every native price, forced reserve, and reset condition. -/
theorem vacuum_history {C : Family G} (hG : G.Simple) (hC : C.Makes)
    {N period order lower : ℕ} (P : Plan C N period order) (Y : Purse)
    (t : ℕ → Pocket) (hCounter : Counter P Y t lower) (hLower : lower ≤ N)
    (hRoom : ∀ i, lower ≤ i → i ≤ N → Room C Y P i (t i))
    (hWave : ∀ i, lower ≤ i → i ≤ N → FixedWave C i (Y.guardBill C.path.levels i)) :
    ∃ L : Trail (C := C) (q := period), Aligned P Y t lower L ∧
      ∀ i, lower ≤ i → i ≤ N →
        (loaded C N period i (P.layers i) (L.atLevel i)).eval =
          (C.path.rep N period i).eval ∧
        |(L.atLevel i).beta - C.path.β N period i| ≤ Y.guardBill C.path.levels i ∧
        |P.predict i - C.path.β N period i| ≤
          (Y.fare + 1) * Currency.weight C.path.levels (Y.sigma - 2) i := by
  obtain ⟨L, hL⟩ := traced P Y hG hC hCounter hLower hRoom hWave
  refine ⟨L, hL, ?_⟩
  intro i hLower hUpper
  have h := hL.costs i hUpper hLower
  exact ⟨h.coupon.value, h.coupon.extraBeta, h.kinetic⟩

end YM.Integration.LocalComparison
