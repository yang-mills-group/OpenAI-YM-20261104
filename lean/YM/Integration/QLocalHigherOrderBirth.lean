import YM.Integration.ActualOriginalQInitialStartup
import YM.Integration.ActualRunSpring

/-! Order chosen from the actual finite marking set before selecting the physical Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalHigherOrderBirth

open Filter Lattice Wilson RG Source Labels Marker RG.Shoot
open PhysicalNext.Repeat.Legato Pressure
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric.Retained
open scoped Classical Topology

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]

def raised (J : Request V) : Request V :=
  { J with order := max (J.order+1) (2*Fintype.card V)
           order_ge_two := J.order_ge_two.trans ((Nat.le_succ _).trans (le_max_left _ _)) }

omit [DecidableEq V] in
theorem surplus (J : Request V) : J.order+1 ≤ (raised J).order := le_max_left _ _

omit [DecidableEq V] in
theorem order (J : Request V) : J.order ≤ (raised J).order := (Nat.le_succ _).trans (surplus J)

omit [DecidableEq V] in
theorem load (J : Request V) : 2*Fintype.card V ≤ (raised J).order := le_max_right _ _

def depth (J : Request V) := 8*((raised J).order+1+2*Fintype.card V+2)

omit [DecidableEq V] in
theorem recovery (J : Request V) :
    8*((raised J).order+1+2*Fintype.card V+2) ≤ 7*(depth J+1) := by
  change depth J ≤ 7*(depth J+1)
  omega

/-- The same foliation, norms, widths, original beta, radius loss and every numerical price. -/
def schedule {C : Family G} {J : Request V} (A : NumericSchedule C J) :
    NumericSchedule C (raised J) where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  admittedCost := A.admittedCost
  admitted_cost_nonnegative := A.admitted_cost_nonnegative
  admitted_cost_ge_one := A.admitted_cost_ge_one
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths := A.cost_covers_widths
  cost_covers_geometry := A.cost_covers_geometry
  cost_covers_units := A.cost_covers_units
  cost_subpower := A.cost_subpower
  pathRate := A.pathRate
  path_rate_positive := A.path_rate_positive
  path_rate_width := A.path_rate_width
  path_rate_cost := A.path_rate_cost
  regular_flat := A.regular_flat
  forced_flat := A.forced_flat

omit [DecidableEq V] in
/-- Both Taylor grades are available at every genuine later patch,
uniformly in the cutoff, period and independent physical marked configurations. -/
theorem eligible (R : Run G) (J : Request V) :
    ∀ᶠ m : ℕ in atTop, ∀ N t : ℕ, m < N →
      (raised J).order+2 ≤ R.family.path.levels.clock.J (m+1) ∧
      depth J ≤ (R.alloy.B.a.clock.op m t).patch.J := by
  obtain ⟨a,ha⟩ := eventually_atTop.1
    (R.family.path.levels.fits.deep.eventually_ge_atTop (max ((raised J).order+2) (depth J)))
  filter_upwards [eventually_ge_atTop a] with m hm N t hmN
  have h := ha (m+1) (by omega)
  refine ⟨(le_max_left _ _).trans h,?_⟩
  rw [(Testing.proceeds R.alloy.B N m t hmN).atStep]
  exact (le_max_right _ _).trans h

variable (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)

/-- All original measured marks, coordinates, directions and their common normalizer agree. -/
theorem packets (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ) :
    ActualOriginalQInitialInput.packets R hG u (raised J) (schedule A) d Q o μ orders =
      ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders := rfl

/-- The exact initially admitted native input, including every forced label and its full carrier. -/
def Born [Nonempty V] (horders : ∀ k, k ≤ (R.metals.p.profile k).order ∧
    k ≤ (R.metals.p.profile k).power) (m : ℕ) : Prop :=
  ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
  ∀ (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (d.level+1) d.period))
    (μ : ℝ) (orders : V → ℕ)
    (hperiod : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (_htop : d.cutoff=d.level+1),
  ∃ hfirst : ActualOriginalQInitialInput.start R hG u J A horders ≤ d.level,
  ∃ I : Numeric.FullPreparedInputAt
    (ActualOriginalQInitialInput.input R hG u J A d Q o μ orders horders hfirst hperiod) 0,
    NativeIntake I ∧ I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1) ∧
    HEq I.input (ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders) ∧
    I.regularPrice=0 ∧ I.forcedPrice=0

theorem both [Nonempty V] (T : Campaign R) (horders : ∀ k, k ≤ (R.metals.p.profile k).order ∧
    k ≤ (R.metals.p.profile k).power) :
    ∀ᶠ m : ℕ in atTop,
      Born R hG u J A horders m ∧ Born R hG u (raised J) (schedule A) horders m ∧
      ∀ N t : ℕ, m < N → (raised J).order+2 ≤ R.family.path.levels.clock.J (m+1) ∧
        depth J ≤ (R.alloy.B.a.clock.op m t).patch.J := by
  filter_upwards [ActualOriginalQInitialAtTop.eventually_prepared R hG u J A T horders,
    ActualOriginalQInitialAtTop.eventually_prepared R hG u (raised J) (schedule A) T horders,
    eligible R J] with m hlo hhi hop
  exact ⟨hlo,hhi,hop⟩

end YM.Integration.QLocalHigherOrderBirth
end
