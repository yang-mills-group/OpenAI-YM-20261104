import YM.Integration.WilsonVacuumPreResetTorusActionRead

/-! Both finite readers use the same radial Taylor coefficients of each original
signed path family at the same physical torus field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusDepositJet
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments WilsonVacuumPreResetTorusPhysicalPeriod
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk Next.Foundations WilsonLimitConstruction WilsonStartup PowerSeries
open scoped Topology BigOperators Classical
open WilsonVacuumPreResetTorusSeason
open WilsonVacuumPreResetTorusSeasonPainting WilsonVacuumPreResetTorusGrade
variable {G:Gauge}{n:Side}
open WilsonVacuumPreResetTorusGrade

theorem sprouted (F:Stationary.Link G n→ℝ)(r t:ℕ)(z:rule (Coarse G) n):
    WilsonVacuumPreResetTorusGrade.evaluated (Blue.sprig F r) t z=PertExtension.Series.Radial.jet F (r+t) z:=by
  rw [WilsonVacuumPreResetTorusGrade.evaluated,Blue.sprig_flash,PowerSeries.coeff_mk,Blue.rayon]
  rfl

theorem original (a:PrismA G)(t:ℕ)(z:rule (Coarse G) n):
    WilsonVacuumPreResetTorusGrade.evaluated (Mosaic.surf a n) t z=Haiku.Coat.trade a.grade a.cells t n z:=by
  by_cases entered:a.grade≤t
  · have shifted:=sprouted (turnSeries a.cells (m:=n)) (a.rise+2) (t-a.grade) z
    have same: WilsonVacuumPreResetTorusGrade.evaluated (Mosaic.surf a n) t z=
        WilsonVacuumPreResetTorusGrade.evaluated (Blue.sprig (turnSeries a.cells (m:=n)) (a.rise+2)) (t-a.grade) z:=by
      simp only [WilsonVacuumPreResetTorusGrade.evaluated,Blue.flash,PowerSeries.coeff_mk,Mosaic.surf,if_pos entered]
    rw [same,shifted,Haiku.Coat.trade,if_pos entered]
    rw [Nat.add_comm (a.rise+2) (t-a.grade)]
  · simp [WilsonVacuumPreResetTorusGrade.evaluated,Blue.flash,Mosaic.surf,entered,Haiku.Coat.trade,Blue.totalR]

theorem classical (K:PathData G)(B:Clip)(t:ℕ)(z:rule (Coarse G) n):
    WilsonVacuumPreResetTorusGrade.evaluated (Blue.sprig (intended B K (m:=n)) 2) t z=Pace.base B K t n z:=by
  rw [sprouted,Nat.add_comm 2 t]
  rfl

theorem loop (K:PathData G)(t:ℕ)(z:rule (Coarse G) n):
    WilsonVacuumPreResetTorusGrade.evaluated (Blue.sprig (turnSeries K.loop (m:=n)) 0) t z=
      Haiku.Coat.clerk (fun _=>Precision.loop K) 0 t n z:=by
  rw [sprouted,Nat.zero_add]
  rfl

end YM.Integration.WilsonVacuumPreResetTorusDepositJet
