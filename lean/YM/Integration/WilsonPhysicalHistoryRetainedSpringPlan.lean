import YM.Integration.WilsonPhysicalHistoryRetainedSpringReading
import YM.Integration.WilsonLimitConstruction.FundedSpringPeriodPlan

/-! Both sides of the actual enrolled period Plan and the signed old clock
discrepancy on it. The coarse source is the complete filed native list. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree PowerSeries Marker
open IterationFour IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
variable (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
variable {d : LocalFormal.Datum R.family Γ} (F : FundedSpringFineInlet.Inlet J A d)
variable (Z : SeriesA G) {σ C : ℝ} (D : RunFundedPeriodAction.PeriodData Z J.order σ C)
local notation "P₀" => FundedSpringPeriodPlan.plan R F Z σ C D
local notation "n₀" => R.family.side d.level d.period

omit [Fintype V]

theorem filed_clock (j : ℕ) (g : ℝ) : pitchDifference R (P₀) j g=0 := by
  unfold pitchDifference
  change (R.alloy.B.kin.alpha d.cutoff j-R.alloy.B.kin.alpha d.cutoff j)+
    ∑ e∈Finset.range (J.order-2+1),
      (coeff (e+2) (pitch R.family.path.levels R.metals.O d.cutoff j)-
        coeff (e+2) (pitch R.family.path.levels R.metals.O d.cutoff j))*g^e=0
  simp

theorem filed_fine (g : ℝ) (U : Config G (R.family.side (d.level+1) d.period)) :
    let j:=d.level+1
    let K:=(R.family.path.rep d.cutoff d.period j).path
    let B:=(R.family.path.levels.params j).clip
    let p:=ActualAnalyticPlanVacuum.radicand R (P₀) j g
    let c:=ActualAnalyticPlanVacuum.coupling R (P₀) j g
    springReading R (P₀) j g U =
      g^2*pitchTail R d.cutoff j J.order g*mainTerm B K U+
      R.alloy.B.kin.alpha d.cutoff j*interaction K U+
        (Integral.temperature g*p)*ActualGradedVacuum.restored F.layers c U := by
  dsimp only
  unfold springReading
  rw [filed_clock R F Z D,zero_add,FundedSpringPeriodPlan.fine R F Z σ C D]
  rfl

theorem filed_previous (g : ℝ) (U : Config G (n₀)) :
    let j:=d.level
    let K:=(R.family.path.rep d.cutoff d.period j).path
    let B:=(R.family.path.levels.params j).clip
    let p:=ActualAnalyticPlanVacuum.radicand R (P₀) j g
    let c:=ActualAnalyticPlanVacuum.coupling R (P₀) j g
    springReading R (P₀) j g U =
      g^2*pitchTail R d.cutoff j J.order g*mainTerm B K U+
      R.alloy.B.kin.alpha d.cutoff j*interaction K U+
        (Integral.temperature g*p)*FundedPeriodAction.rendered (n₀) Z c U := by
  dsimp only
  unfold springReading
  rw [filed_clock R F Z D,zero_add,FundedSpringPeriodPlan.coarse R F Z σ C D,
    ←D.restored (n₀) (A.outputNorm d.level)]
  rfl

end YM.Integration.OriginalMarkedRunAction
