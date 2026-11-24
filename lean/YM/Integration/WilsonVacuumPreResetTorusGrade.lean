import YM.Integration.WilsonVacuumPreResetTorusSeason
import YM.WilsonCoeffUV.VacuumLaw

/-! Complete finite unreset action differences have exactly the registered
positive angular ranks, even when their omitted vacuum term grows with volume. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusGrade
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
open WilsonCoeffUV.Blue WilsonCoeffUV.Fk WilsonCoeffUV.Wheel PowerSeries
open WilsonVacuumPreResetTorusSeason
variable {G:Gauge}{n:Side}

def evaluated (P:PChart G n)(t:ℕ)(z:rule (Coarse G) n):ℝ:=
  MvPolynomial.eval z (coeff t (Blue.flash P))

theorem positive (P:PChart G n)(bound:shellK 2 P)(t:ℕ)(z w:rule (Coarse G) n):
    evaluated P t z-evaluated P t w=
      ∑l∈Finset.range (t+2),(MvPolynomial.eval z (Blue.paint (l+1) (P t (l+1)))-
          MvPolynomial.eval w (Blue.paint (l+1) (P t (l+1)))):=by
  classical
  have finite:still (P t) (t+2+1):=fun r hr=>bound t r (by omega)
  have flat:MvPolynomial.eval z (Blue.paint 0 (P t 0))=MvPolynomial.eval w (Blue.paint 0 (P t 0)):=by
    change MvPolynomial.eval z (∑x:Fin 0 → Woods G n,P t 0 x • ∏i,MvPolynomial.X (x i))=
      MvPolynomial.eval w (∑x:Fin 0 → Woods G n,P t 0 x • ∏i,MvPolynomial.X (x i))
    simp
  simp only [evaluated,Blue.flash,coeff_mk,Blue.visible finite,map_sum,← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ',flat,sub_self,add_zero]

theorem original (R:Run G)(simple:G.Simple){N j:ℕ}(earlier:j<N)(n:Side):
    shellK 2 (unripe R.family.path.levels R.metals.O N j
      (story R.family.path.levels R.metals.O N (j+1)).1 n):=by
  let A:=R.family.path.levels
  let S:=mStep A n j
  let F:=repeatF S
  let Q:=roam A N j n
  let P:=(story A R.metals.O N (j+1)).1 (n*(loose A j).L)
  have actual:=(finite_sampler (A:=A) simple R.alloy.B.ratio earlier n).prescription
  rw [actual.2.1]
  exact winter_band S F (freeForms A N (j+1)) (freeForms A N j) Q R.alloy.B.ratio
    ((old A R.metals.O simple R.alloy.B.ratio N (j+1) earlier).basis _).lamp

end YM.Integration.WilsonVacuumPreResetTorusGrade
