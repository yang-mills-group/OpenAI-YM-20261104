import YM.Integration.WilsonNeutralFiledFieldReversion
import YM.Integration.WilsonNeutralSignedPolynomialRate
import YM.Integration.WilsonOriginalMeasuredOccupiedForest
import YM.Integration.WilsonVacuumPreResetIndependentForecast

/-! The true reverse change of coupling and field, using the measured
kinetic coordinate on every nonbare date of a single Wilson trajectory.
It acts on the complete spatial field and its own normalized transfer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralOriginalFieldReversion
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.alloy.B.a

open WilsonVacuumPreResetTorusScalarClock

open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi

open Primitives.TwoWave.RealSlice PertExtension.Series
open Next.Free FormalBulk08.Lotus FormalBulk08.Mesa
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Roof
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)


open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical



open WilsonNeutralSignedPolynomialRate WilsonNeutralFiledFieldReversion
open WilsonOriginalMeasuredOccupiedForest WilsonVacuumPreResetDatedDeposit WilsonVacuumPreResetTorusDeposit
open Comparison.RG02 Comparison.RG02.Adjacent AllOrder.Floe.Step.PlanV
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)

include R in
theorem rate (u:G.ColorIndex)(hs:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit){N i:ℕ}(cut:i<N):
    pitch (levels R) (ratio R) N i=kinetic R wood u N i:= by
  rw [WilsonVacuumPreResetIndependentForecast.pitch_eq R u hs v rows cut]
  unfold WilsonVacuumPreResetIndependentForecast.prescription kinetic
  rw [WilsonNeutralAppointedForestStep.vacuum R wood u grant]


theorem marked (u:G.ColorIndex)(hs:G.Simple)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit){U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
    {N m h i:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (quiet:Read R N m h Z π Γ)(lo:m ≤ i)(cut:i < N)(starts:Γ i 0=0)
    {E V:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype V]
    (source:Adjacent.Display E)(L:E→ₗ[ℝ](V→ℝ))(T:Pap V){e p:ℕ}(eligible:e≤h+2)(retained:e≤p)
    (z:E)(scale:ℂ)(heard:∀j≤p,∀t:ℝ,source j (t • z)=scale*WilsonNeutralSignedPolynomialRate.read L T j (t • z)):
    let H:=kinetic R wood u N i
    Adjacent.born source ((Rebirth.caliber (Γ i) starts).back (h+2)) 0 p e z=
      scale*WilsonNeutralSignedPolynomialRate.read L (canter (bookH H) (bookU H) V T) e z := by
  intro H
  have tariff:=(WilsonVacuumPreResetMeasuredCaliber.settled R quiet.course lo cut starts).2.2.2
  rw [rate R u hs v rows grant cut] at tariff
  exact WilsonNeutralSignedPolynomialRate.original tariff source L T eligible retained z scale heard

theorem original (u:G.ColorIndex)(hs:G.Simple)(o:Loc G 1)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit){U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
    {N m h i:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (quiet:Read R N m h Z π Γ)(lo:m ≤ i)(cut:i < N)(starts:Γ i 0=0)
    {d D:ℕ}(depth:d<D)(hd:d≤R.family.path.levels.clock.J (i+1))(per:ℕ)(b:Letter (R.family.labels.level d))
    (f:Studio D){e p:ℕ}(eligible:e≤h+2)(retained:e≤p)
    {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
    (source:Adjacent.Display E)(L:E→ₗ[ℝ](wire G (R.family.side i per)→ℝ))(z:E)(scale:ℂ)
    (heard:∀j≤p,∀t:ℝ,source j (t • z)=scale*WilsonNeutralSignedPolynomialRate.read L
      (before R wood u depth N i b f (R.family.side i per)) j (t • z)):
    Adjacent.born source ((Rebirth.caliber (Γ i) starts).back (h+2)) 0 p e z=
      scale*WilsonNeutralSignedPolynomialRate.read L (after R wood u depth N i b f (R.family.side i per)) e z:=by
  have applied:=marked R u hs v rows grant quiet lo cut starts source L _ eligible retained z scale heard
  dsimp only at applied
  rw [WilsonNeutralFiledFieldReversion.original R wood u depth grant N i hs o cut hd per b f] at applied
  exact applied

end YM.Integration.WilsonNeutralOriginalFieldReversion
end
