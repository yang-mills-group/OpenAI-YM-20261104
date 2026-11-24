import YM.Integration.FullQLocalRetainedOutput
import YM.Integration.LocalComparisonBarePreparationAt
import YM.Integration.LocalComparisonPreResetDensity
import YM.Integration.LocalComparisonPhysicalReadout

/-! Auxiliary zero marked sources for an unmarked vacuum comparison on an
admitted layout. The physical carrier, forced vacuum gas and mask predicates,
regular error, calibration, analytic vacuum layers and their action are fixed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.VacuumAuxiliaryInput

open Filter Lattice Wilson RG Marker IterationFour.Vacuum
open RG3.Script.Picnic Comparison.RG02
open LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R} {D : V → ComparisonDensity.Address.Orbit}

/-- The original vacuum color with zero auxiliary source insertions. -/
def colors {n : Side} (W : Bulk.Colors R G n) : Bulk.Colors R G n :=
  { W with mark := 0, power := 0 }

omit [Fintype V] in
private theorem well {n : Side} {W : Bulk.Colors R G n} (h : Bulk.Well W) :
    Bulk.Well (colors W) := by
  have hz := (Bulk.Colors.no_hole G n R).1
  exact ⟨h.suppose_vac, hz.suppose_mark, h.natural, hz.gauges, h.envelope, hz.prices⟩

/-- A genuine zero-insertion bank on the same marked alphabet. -/
def packets (D : V → ComparisonDensity.Address.Orbit) (G : Gauge) (n : Side)
    (R : Census V) : MarkedPackets D G n R where
  mode := fun _ => R.quiet
  rank := fun _ => 0
  power := fun _ => 0
  packet := fun _ => none
  marked := by simp
  rankCap := 0
  powerCap := 0
  rank_bounded := by simp
  power_bounded := by simp
  nonnegative_grade := by simp

theorem read {n : Side} (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (packets D G n R).read x g U = 0 := by
  simp [MarkedPackets.read, MarkedPackets.term, packets, Poly.send_zero]

private theorem convention {n : Side} {W : TestSpace D → Bulk.Colors R G n}
    {P : MarkedPackets D G n R} (h : InputColors W P) :
    InputColors (fun x => colors (W x)) (packets D G n R) where
  well x := well (h.well x)
  vacuum := h.vacuum
  power _ _ := rfl
  marks x g _ U := by
    rw [read]
    simp [Integral.markedLog, Multi.lit, colors, Poly.send_zero]

omit [Fintype V] in
theorem paid {n : Side} (p : BudgetPoint) (address : V → Support n)
    (region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n)
    (w : V → ℝ) (g width budget : ℝ) (hw : ∀ v, 0 < w v)
    (hwidth : 0 < width) (hbudget : 0 ≤ budget) :
    (packets D G n R).Paid p address region w g width budget 0 0 where
  width_pos := hwidth
  positive := hw
  coefficient := by simp [packets]
  paths := by simp [packets]
  addresses := by simp [packets]
  symmetry := by simp [packets]
  reads := by simp [packets]
  multilinear := by simp [packets]
  roots v := by
    simpa [packets, Census.quiet] using
      (show SumBudget (fun _ : ℕ => (0 : ℝ)) budget from
        ⟨fun _ => le_rfl, summable_zero, by simpa only [tsum_zero] using hbudget⟩)
  cover := by simp [packets]
  width_reserved := by simpa using (div_nonneg hwidth.le (by norm_num : (0 : ℝ) ≤ 4))

/-- All unmarked analytic data, including the complete coupling-ray action,
come from the provided physical input. -/
def analytic (F : AnalyticInput J A datum) : AnalyticInput J A datum :=
  { F with
    colors := fun x => colors (F.colors x)
    packets := packets J.tests G _ R
    convention := convention F.convention
    rank_bounded := Nat.zero_le _
    power_bounded := Nat.zero_le _
    whole_input := {
      standard := fun x => ⟨well (F.whole_input.standard x).1, (F.whole_input.standard x).2⟩
      input_summable := F.whole_input.input_summable
      inputExtension := F.whole_input.inputExtension
      formalInputExtension := F.whole_input.formalInputExtension
      input_extension_value := F.whole_input.input_extension_value
      formal_input_extension_value := F.whole_input.formal_input_extension_value
      input_extension_smooth := F.whole_input.input_extension_smooth
      formal_input_extension_smooth := F.whole_input.formal_input_extension_smooth
      input_whole := F.whole_input.input_whole }
    coverOffset := 0
    coverSlope := 0
    cover_cost := by simpa using A.admitted_cost_ge_one datum.level
    input_paid := paid (A.inputNorm datum.level) F.inputAddresses F.inputRegion
      (fun v => F.inputRadii v / F.kernelCosts v) _ _ _
      (fun v => div_pos (F.input_radius_positive v) (F.kernel_positive v))
      (A.input_width_pos datum.level) (A.admitted_cost_nonnegative datum.level) }

/-- Prepare a physical vacuum with the exact full gas on its given carrier.
The affine-null payload and kinetic calibration are paid separately. -/
def atCarrier (F : AnalyticInput J A datum)
    (Q : PhysicalCarrier C datum.cutoff datum.period (datum.level + 1))
    (hWF : WellFormed (A.inputNorm datum.level) Q.rep)
    (b : ℝ) (hb : b ≤ J.inheritedConstant *
      Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^
        ((J.order : ℝ) + 1 - J.eta))
    (E : Payload G (C.side (datum.level + 1) datum.period))
    (hE : E.Invoice (A.inputNorm datum.level) b)
    {η : ℝ} (B : CalibrationPresentation Q.rep (A.inputNorm datum.level) η)
    (hExp : ∀ U, Q.rep.exponent U = Q.rep.scalar -
      ((C.path.rep datum.cutoff datum.period (datum.level + 1)).path.inChannels
        Q.rep.clip Q.rep.p (C.path.β datum.cutoff datum.period (datum.level + 1)) U +
        Render.renders (Render.prefactor (Pert.Asymptotics.regulatorRun C
          datum.cutoff datum.period (datum.level + 1))) Q.rep.p U F.layers) -
        E.amount (A.inputNorm datum.level) U - B.amount U)
    (T : Taste (TestSpace J.tests) F.fineRoots Q.rep R)
    (x₀ : TestSpace J.tests) (hLayout : (T.leaf x₀).Active)
    (hGas : Q.rep.activities.KBound (C.path.levels.budget (datum.level + 1))
      (C.path.levels.clock.forcedAllowance (datum.level + 1)))
    (hpack : F.packets = packets J.tests G _ R) : FullPreparedInputAt F η := {
    carrier := Q
    wellFormed := hWF
    inherited := b
    inherited_nonnegative := Payload.nonneg hE
    inherited_bound := hb
    error := E
    error_paid := hE
    calibration := B
    exponent := hExp
    input := vacuumRemainder T
    multilinear := {
      regular := fun _ _ => RG3.Held.Letter.still
      forced := fun _ _ _ => RG3.Held.Letter.still
      unit := fun _ => RG3.Held.Letter.still
      captions := fun _ => RG3.Held.Letter.still }
    input_retains := {
      origins := F.input_origins
      regular := by rintro _ _ ⟨_, _, h⟩; exact (h rfl).elim
      forced := by rintro _ _ _ ⟨_, _, h⟩; exact (h rfl).elim
      captions := by rintro _ _ ⟨_, h⟩; exact (h rfl).elim }
    regularPrice := 0
    forcedPrice := 0
    forced_bound := J.forced_constant_nonnegative
    prepared := PreparedWithRemainderAt.of_bare_factorization
      datum.cutoff datum.period (datum.level + 1) (A.inputNorm datum.level)
      (Handoff.legacyCarrier Q) F.fineRoots (vacuumRemainder T)
      F.colors F.packets F.inputRadii (envelopeProduct F.kernelCosts)
      x₀ (vacuumRemainder_active T x₀ hLayout x₀) F.convention
      F.input_radius_positive (envelopeProduct_positive F.kernel_positive)
      (by simp [envelopeProduct, Census.quiet])
      (fun U => (PreResetDensity.gasSeries (p := Q.rep.p) hGas).absolute U)
      (by
        intro x U
        calc
          _ = (Q.rep.eval U : ℂ) • (1 : Poly R) :=
            vacuumRemainder_density T x U
              ((PreResetDensity.gasSeries (p := Q.rep.p) hGas).absolute U)
          _ = _ := by
            change _ = (Q.rep.eval U : ℂ) • Poly.pass (F.packets.read x _ U)
            rw [hpack, read, Extra.Trajectories.pass_zero]) }

variable {F : AnalyticInput J A datum} {η : ℝ} (I : FullPreparedInputAt F η)
    (T : Taste (TestSpace J.tests) F.fineRoots I.carrier.rep R)
    (x₀ : TestSpace J.tests) (hLayout : (T.leaf x₀).Active)
    (hI : Retained.NativeIntake I)

/-- Start a vacuum-only comparison at this same representation. Zero marked
prices are proved from its active layout and summable original vacuum gas. -/
def prepared : FullPreparedInputAt (analytic F) η :=
  atCarrier (analytic F) I.carrier I.wellFormed I.inherited I.inherited_bound
    I.error I.error_paid I.calibration I.exponent T x₀ hLayout hI.original rfl

/-- The inherited unmarked price is literal. Every vacuum weight and every
regular or forced vacuum row is carried by the identical represented carrier. -/
theorem data :
    (prepared I T x₀ hLayout hI).carrier = I.carrier ∧
    (prepared I T x₀ hLayout hI).inherited = I.inherited ∧
    (prepared I T x₀ hLayout hI).error = I.error ∧
    (prepared I T x₀ hLayout hI).calibration = I.calibration ∧
    (analytic F).layers = F.layers ∧
    (prepared I T x₀ hLayout hI).regularPrice = 0 ∧
    (prepared I T x₀ hLayout hI).forcedPrice = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem intake : Retained.NativeIntake (prepared I T x₀ hLayout hI) :=
  ⟨hI.original, hI.reserved, le_rfl, zero_le_one⟩

/-- The already-paid remainder supplies an active padding layout at the
canonical zero test, so an auxiliary source needs no fresh layout witness. -/
private def template : Taste (TestSpace J.tests) F.fineRoots I.carrier.rep R :=
  pullback (fun _ : TestSpace J.tests => zeroIndependentTests J.tests)
    (priceNormalized (envelopeProduct F.kernelCosts)
      (pullback (testInclusion J.tests) I.prepared.remainder))

private theorem template_active (x : TestSpace J.tests) : ((template I).leaf x).Active :=
  I.prepared.remainder_price.budget.active (zeroIndependentTests J.tests)

/-- A prepared Wilson input and its native intake already supply the full
auxiliary vacuum on that carrier, with both marked input prices zero. -/
def project : FullPreparedInputAt (analytic F) η :=
  prepared I (template I) (testInclusion J.tests (zeroIndependentTests J.tests))
    (template_active I _) hI

theorem project_data :
    Retained.NativeIntake (project I hI) ∧
      (project I hI).carrier = I.carrier ∧ (project I hI).inherited = I.inherited ∧
      (project I hI).error = I.error ∧ (project I hI).calibration = I.calibration ∧
      (project I hI).regularPrice = 0 ∧ (project I hI).forcedPrice = 0 :=
  ⟨intake I _ _ _ hI, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Enlarging the calibration cap retains each original row, germ, mask
and its exact physical amount. -/
def largerCalibration {n : Side} {Q : Rep G n} {p : BudgetPoint} {a b : ℝ}
    (L : CalibrationPresentation Q p a) (h : a ≤ b) : CalibrationPresentation Q p b :=
  { L with
    size_nonnegative := L.size_nonnegative.trans h
    regular_total := fun x => ⟨(L.regular_total x).1, (L.regular_total x).2.1,
      (L.regular_total x).2.2.trans h⟩
    full_hit := fun x => ⟨(L.full_hit x).1, (L.full_hit x).2.1,
      (L.full_hit x).2.2.trans h⟩ }

/-- Use the one fixed positive calibration envelope at startup even when
the initial native expansion supplies an exact zero calibration. -/
def raiseCap {b : ℝ} (h : η ≤ b) : FullPreparedInputAt F b :=
  { I with calibration := largerCalibration I.calibration h }

include hI in
theorem raiseCap_intake {b : ℝ} (h : η ≤ b) :
    Retained.NativeIntake (raiseCap I h) :=
  ⟨hI.original, hI.reserved, hI.ordinary_nonnegative, hI.ordinary_small⟩

end YM.Integration.VacuumAuxiliaryInput
