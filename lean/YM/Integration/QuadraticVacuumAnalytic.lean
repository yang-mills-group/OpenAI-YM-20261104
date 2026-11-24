import YM.Integration.VacuumAuxiliaryInput
import YM.Integration.ActualLayerFineAction
import YM.Integration.ActualRunFixedOrders
import YM.Integration.ActualStartupVacuumPackets

/-! Analytic intake of the unmarked quadratic comparison on the original
trajectory. There are no additional legal vacuum layers at this order.
Consequently one fixed schedule supplies all widths and layer costs for
unboundedly many calls on the exact Wilson histories. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.QuadraticVacuumAnalytic

open Filter Lattice Wilson RG Marker
open Comparison.RG02 PhysicalNext.Repeat.Legato
open IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {D : V → ComparisonDensity.Address.Orbit}

/-- The empty graded list is genuinely paid at every positive width and
budget at least one, keeping the original cover cost. -/
def empty_layers (n : Side) (p : BudgetPoint) (order cap : ℕ)
    (width budget : ℝ) (hw : 0 < width) (hb : 1 ≤ budget) :
    GradedVacuumLayers ([] : List (Piece G n)) p order cap width budget where
  packets := {
    atom := fun a _ => ActualStartupVacuumPackets.zeroAtom G a.rank
    rank_bounded := by simp
    invariant := by simp
    original_action := by simp
    support := by simp
    pieceCost := fun _ => 0
    piece_cost_nonnegative := by simp
    exponential := by simp
    total := by simpa using zero_le_one.trans hb
    coverOffset := 0
    coverSlope := 0
    cover := by simp
    width_reserved := by simpa using (div_nonneg hw.le (by norm_num : (0 : ℝ) ≤ 4))
    cover_cost := by simpa using hb }
  orders := by simp [Render.gradings]
  leading_rank := by simp

private theorem convention (n : Side) :
    InputColors (fun _ : TestSpace D => Bulk.Colors.noHole G n Γ)
      (VacuumAuxiliaryInput.packets D G n Γ) where
  well _ := (Bulk.Colors.no_hole G n Γ).1
  vacuum _ _ := rfl
  power _ _ := rfl
  marks x g _ U := by
    rw [VacuumAuxiliaryInput.read]
    simp [Integral.markedLog, Multi.lit, Bulk.Colors.noHole, Poly.send_zero]

variable (R : Run G) (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family Γ)

/-- An actual coarse chart with an admitted ambient mark alphabet and zero
auxiliary inserted sources. The genuine unmasked vacuum and its gauge action
are exhibited through every requested derivative order. -/
def input
    (hwhole : ∀ v, ∃ k w : ℕ, J.tests v = ⟨.whole, k, w⟩)
    (roots : V → Site (R.family.side (d.level + 1) d.period))
    (region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood)
      (R.family.side (d.level + 1) d.period))
    (hperiod : J.physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (hi : J.inputFieldOrder ≤ (R.family.path.levels.budget (d.level + 1)).order)
    (hd : J.inputDistanceOrder ≤ (R.family.path.levels.budget (d.level + 1)).power)
    (ho : J.outputFieldOrder ≤ (R.family.path.levels.budget d.level).order)
    (hp : J.outputDistanceOrder ≤ (R.family.path.levels.budget d.level).power)
    (href : ∀ v, R.family.ref (J.outputWeight v) ≤ d.level) :
    AnalyticInput J A d := by
  let n := R.family.side (d.level + 1) d.period
  let W := fun _ : TestSpace J.tests => Bulk.Colors.noHole G n Γ
  let P := VacuumAuxiliaryInput.packets J.tests G n Γ
  let H := empty_layers (G := G) n (A.inputNorm d.level) J.order J.vacuumRankCap
    (A.inputWidth d.level) (A.admittedCost d.level) (A.input_width_pos _) (A.admitted_cost_ge_one _)
  have hW : InputColors W P := convention n
  have hV : ∀ x, (W x).vac = ActualGradedVacuum.restored [] := by
    intro x; funext g U; rfl
  exact {
    whole_tests := hwhole
    layers := []
    layers_paid := by simp [Render.permits]
    vacuum := H
    fineRoots := roots
    coarseRoots := fun v => (R.family.path.levels.clock.op d.level d.period).ratio.parent (roots v)
    roots := fun _ => rfl
    colors := W
    packets := P
    convention := hW
    rank_bounded := Nat.zero_le _
    power_bounded := Nat.zero_le _
    whole_input := Classical.choice (ActualLayerFineAction.whole_action R Γ J d H
      (A.input_width_pos _) W P hW hV)
    inputRadii := fun _ => A.radiusLoss d.level
    outputRadii := fun _ => 1
    kernelCosts := fun _ => 1
    input_radius_positive := fun _ => A.radius_loss_positive _
    output_radius_positive := fun _ => zero_lt_one
    kernel_positive := fun _ => zero_lt_one
    radius_admission := by simp
    inputAddresses := fun v => {roots v}
    input_origins := fun _ => Finset.mem_singleton_self _
    inputRegion := region
    coverOffset := 0
    coverSlope := 0
    cover_cost := by simpa using A.admitted_cost_ge_one d.level
    input_paid := VacuumAuxiliaryInput.paid (A.inputNorm d.level) (fun v => {roots v})
      region (fun _ => A.radiusLoss d.level / 1) _ _ _
      (fun _ => div_pos (A.radius_loss_positive _) zero_lt_one)
      (A.input_width_pos _) (A.admitted_cost_nonnegative _)
    physical_period := hperiod
    input_field_admitted := hi
    input_distance_admitted := hd
    output_field_admitted := ho
    output_distance_admitted := hp
    primary_admitted := href }

/-- Admission occurs before the cutoff, torus, marked layout, physical
field and chart. Input and output consume just the original fixed schedule. -/
theorem eventually_input
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (hwhole : ∀ v, ∃ k w : ℕ, J.tests v = ⟨.whole, k, w⟩) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = m →
      J.physicalPeriodLower ≤ (R.family.S.period d.period).val →
      ∀ (roots : V → Site (R.family.side (d.level + 1) d.period))
        (region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood)
          (R.family.side (d.level + 1) d.period)),
      ∃ F : AnalyticInput J A d, F.layers = [] ∧
        F.packets = VacuumAuxiliaryInput.packets J.tests G _ Γ ∧ F.fineRoots = roots ∧
        F.inputRegion = region := by
  let order := max J.inputFieldOrder J.inputDistanceOrder
  let first := (Finset.univ : Finset V).sup fun v => R.family.ref (J.outputWeight v)
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop order,
    eventually_ge_atTop first] with m hm hfirst d hd hperiod roots region
  obtain ⟨ho, hp⟩ := ActualRunFixedOrders.budget_orders R hprofile m
  obtain ⟨hi, hq⟩ := ActualRunFixedOrders.budget_orders R hprofile (m+1)
  have hn := hm.trans (R.family.path.levels.fits.mono (Nat.le_succ m))
  have ho' : J.inputFieldOrder ≤ order := le_max_left _ _
  have hp' : J.inputDistanceOrder ≤ order := le_max_right _ _
  refine ⟨input R J A d hwhole roots region hperiod (hd ▸ (ho'.trans hn).trans hi)
    (hd ▸ (hp'.trans hn).trans hq) (hd ▸ ((J.field_reserve.trans ho').trans hm).trans ho)
    (hd ▸ ((J.distance_reserve.trans hp').trans hm).trans hp) ?_,
    rfl, rfl, rfl, rfl⟩
  intro v
  exact hd ▸ (Finset.le_sup (f := fun i => R.family.ref (J.outputWeight i))
    (Finset.mem_univ v)).trans hfirst

/-- All layers of the actual selected quadratic plan are the very empty
list supplied above, including its coefficientwise fine input. -/
theorem selected_layers {K : NumericPrices A} {F : AnalyticInput J A d}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path}
    (M : AnalyticOutput caps Y K F) (horder : J.order = 2) (i : ℕ) (hi : i ≤ d.cutoff) :
    M.plan.layers i = [] := by
  cases h : M.plan.layers i with
  | nil => rfl
  | cons e es =>
    have hmem : e ∈ M.plan.layers i := by rw [h]; exact List.mem_cons_self
    obtain ⟨hlo, hhi⟩ := M.plan.orders i hi e hmem
    omega

end YM.Integration.QuadraticVacuumAnalytic
