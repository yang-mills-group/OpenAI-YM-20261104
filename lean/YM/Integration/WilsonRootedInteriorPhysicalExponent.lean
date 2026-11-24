import YM.Integration.ActualRequestedStartupPhysical
import YM.Integration.ActualOriginalQInitialPreparation

/-! The signed discrepancy for the actual original interior representative and its selected fresh album. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedInteriorPhysicalExponent
open Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric LocalComparison
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "X" => R.family.path.rep N per j
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per j

/-- The full original masked regular inventory minus the independently specified rendered layers. -/
def discrepancy (L : List (Piece G (R.family.side j per))) (U : Config G (R.family.side j per)) : ℝ :=
  (∑' i : ℕ,(X).activities.regularOccurrence (X).p i U) - Render.renders (Render.prefactor (g)) (X).p U L

theorem exponent (L : List (Piece G (R.family.side j per))) (U : Config G (R.family.side j per)) :
    (X).exponent U=(X).scalar-((X).path.inChannels (X).clip (X).p (R.family.path.β N per j) U+
      Render.renders (Render.prefactor (g)) (X).p U L)-discrepancy R (N:=N) L U := by
  change (X).scalar-_- (X).activities.additive (X).p U=_
  unfold discrepancy
  change (X).scalar-_- (X).activities.additive (X).p U=
    (X).scalar-(_+_)-((X).activities.additive (X).p U-_)
  ring

/-- The very same covered gas multiplies the exponent on every configuration. -/
theorem density (L : List (Piece G (R.family.side j per))) (U : Config G (R.family.side j per)) :
    (X).eval U=Real.exp ((X).scalar-((X).path.inChannels (X).clip (X).p (R.family.path.β N per j) U+
      Render.renders (Render.prefactor (g)) (X).p U L)-discrepancy R (N:=N) L U)*(X).activities.gas (X).p U := by
  rw [Rep.eval,exponent R L U]

/-- At a genuine interior `AnalyticInput`, the condition involves only its actual regulator,
selected layers, and the two actual paid functions. -/
theorem physical_iff {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {d : LocalFormal.Datum R.family Γ} (F : AnalyticInput J A d)
    (E K : Config G (R.family.side (d.level+1) d.period)→ℝ) :
    let Y := R.family.path.rep d.cutoff d.period (d.level+1)
    (∀U,Y.exponent U=Y.scalar-(Y.path.inChannels Y.clip Y.p (R.family.path.β d.cutoff d.period (d.level+1)) U+
      Render.renders (Render.prefactor (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1))) Y.p U F.layers)-E U-K U) ↔
    ∀U,E U+K U=discrepancy R (N:=d.cutoff) (per:=d.period) (j:=d.level+1) F.layers U := by
  dsimp only
  constructor
  · intro h U
    linarith only [h U,exponent R (N:=d.cutoff) (per:=d.period) (j:=d.level+1) F.layers U]
  · intro h U
    linarith only [h U,exponent R (N:=d.cutoff) (per:=d.period) (j:=d.level+1) F.layers U]

/-- At the genuine ultraviolet opening, the full original chip pays exactly this discrepancy. -/
theorem startup {V : Type} (J : Request V) (A : NumericSchedule R.family J) (T : Campaign R)
    (m per : ℕ) (U : Config G (R.family.side (m+1) per)) :
    discrepancy R (N:=m+1) (per:=per) (j:=m+1)
      (ActualStartupInvoice.paidAlbum G (R.family.side (m+1) per) (A.inputNorm m)
        (R.family.path.levels.params (m+1)) J.order (A.inputWidth m)) U =
      (ActualStartupMaskedAction.remainder R (m+1) per J.order).amount (A.inputNorm m) U := by
  have top:=ActualRequestedStartupPhysical.physical_exponent R J A T m per U
  have zero:=ActualStartupCalibration.calibration_amount R (m+1) per (A.inputNorm m)
    (ActualRequestedStartupPhysical.threshold R J A m per) U
  change (ActualRequestedStartupPhysical.calibration R J A m per).amount U=0 at zero
  dsimp only at top
  rw [zero,sub_zero] at top
  linarith only [top,exponent R (N:=m+1) (per:=per) (j:=m+1) (ActualStartupInvoice.paidAlbum G
    (R.family.side (m+1) per) (A.inputNorm m) (R.family.path.levels.params (m+1)) J.order (A.inputWidth m)) U]

end YM.Integration.WilsonRootedInteriorPhysicalExponent
