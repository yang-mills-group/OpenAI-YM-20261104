import YM.Integration.WilsonVacuumPreResetTorusDeposit
import YM.Integration.WilsonVacuumPreResetTorusDepositJet

/-! The full trade at an age is the sum of the independent signed path
coefficients originally deposited there, including repeated placements. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusDepositRows
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
open WilsonVacuumPreResetTorusDeposit WilsonVacuumPreResetTorusGrade

private theorem null (i:Age)(t:ℕ)(z:rule (Coarse G) n):
    Haiku.Coat.trade i.e (fun _ : ℕ=>Extra.Iteration.blank G i.r) t n z=0:=by
  have empty:turnSeries (fun _ : ℕ=>Extra.Iteration.blank G i.r) (m:=n)=0:=by
    ext x
    simp [turnSeries,Patch.average,Precision.uncut,Atom.unmasked,Extra.Iteration.blank,Atom.poly]
  unfold Haiku.Coat.trade
  split <;> simp [empty,PertExtension.Series.Radial.jet]

private theorem plus {j:ℕ}{P Q:ℕ→Atom G j}{σ C D:ℝ}(hs:0<σ)
    (hp:Extra.Iteration.Charged P σ C)(hq:Extra.Iteration.Charged Q σ D)
    (e t:ℕ)(z:rule (Coarse G) n):
    Haiku.Coat.trade e (Extra.Iteration.join P Q) t n z=
      Haiku.Coat.trade e P t n z+Haiku.Coat.trade e Q t n z:=by
  have bodies:turnSeries (Extra.Iteration.join P Q) (m:=n)=turnSeries P+turnSeries Q:=
    funext fun x=>Extra.Iteration.action_join hs hp hq (Stationary.input G n x)
  by_cases h:e≤t
  · simp only [Haiku.Coat.trade,if_pos h,bodies]
    exact AllOrder.Laplace.jet_add (turns_analytic _ hs hp).contDiffAt
      (turns_analytic _ hs hq).contDiffAt _
  · simp [Haiku.Coat.trade,h]

def subtotal (i:Age)(t:ℕ)(z:rule (Coarse G) n):SeriesA G→ℝ
  | []=>0
  | a::T=> if address a=i then WilsonVacuumPreResetTorusGrade.evaluated (Mosaic.surf a n) t z+
      subtotal i t z T else subtotal i t z T

theorem original (Z:SeriesA G){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)(grades:∀a∈Z,3≤a.grade)
    (i:Age)(t:ℕ)(z:rule (Coarse G) n):
    Haiku.Coat.trade i.e (bank Z i) t n z=subtotal i t z Z:=by
  induction Z with
  | nil => exact null i t z
  | cons a T ih =>
    have drawT:Draw T σ C:=⟨draw.1,fun x hx=>draw.2 x (List.mem_cons_of_mem _ hx)⟩
    have gradesT (x:PrismA G)(hx:x∈T):3≤x.grade:=grades x (List.mem_cons_of_mem _ hx)
    have entered:=grades a (List.mem_cons_self ..)
    have recursive:=ih drawT gradesT
    by_cases hit:address a=i
    · subst i
      have received:=WilsonVacuumPreResetTorusDeposit.quoted T drawT.2
        (fun x hx=>lt_of_lt_of_le (by decide :0<3) (gradesT x hx)) (address a)
      have adding:=plus width (draw.2 a (List.mem_cons_self ..)).toll received.pay
        (address a).e t z
      have head : Haiku.Coat.trade (address a).e a.cells t n z=
          WilsonVacuumPreResetTorusGrade.evaluated (Mosaic.surf a n) t z:=by
        rw [(coordinates a entered).1,WilsonVacuumPreResetTorusDepositJet.original]
      simp only [WilsonVacuumPreResetTorusDeposit.bank,subtotal]
      exact adding.trans (congrArg₂ (·+·) head recursive)
    · simpa only [WilsonVacuumPreResetTorusDeposit.bank,subtotal,dif_neg hit,if_neg hit] using recursive

end YM.Integration.WilsonVacuumPreResetTorusDepositRows
