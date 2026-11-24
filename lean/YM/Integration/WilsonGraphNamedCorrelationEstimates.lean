import YM.Integration.WilsonGraphIncumbentGraphPublication
import YM.Integration.WilsonGraphIncumbentCorrelationPublication

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphNamedCorrelationEstimates
open YangMills.Matching
open WilsonGraphPaperPublication WilsonGraphPublishedReturnLaws
open WilsonGraphIncumbentWardSeriesPublication

universe u

/-- The complete measured estimates for the independently issued graph on each public period. -/
theorem atPeriods (g : YangMills.GaugeGroup) (hg : g.IsSimple)
    (p : ℕ → ℕ) (hp : StrictMono p) :
    CorrelationOnly.Estimates (_root_.IssuedMaxwell.GraphCoefficients.issued g)
      (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
      (measurementOnPick.{u} g hg p hp) := by
  let M := _root_.IssuedMaxwell.GraphCoefficients.issued g
  let W := measurementOnPick.{u} g hg p hp
  have group : CorrelationOnly.FiledCorrelations M
      (WilsonGraphGroupPositionReference.external g hg).conversion.conversion W := by
    apply (congrArg (fun C : Conversion (YangMills.maxwellReference g) =>
      CorrelationOnly.FiledCorrelations M C W) (filedOnGroup.{u} g hg)).mpr
    exact (WilsonGraphGraphPaperCorrelations.maxwellAndAllOrdersOnPick hg
      (construction.{u} g hg) (publicPick.{u} g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)
      (WilsonGraphIncumbentGraphPublication.atPeriods.{u} g hg) p hp).1
  refine ⟨fun n d => ⟨0, group.tested n d⟩, group.compact, group.jets,
    phaseOnPick.{u} g hg p hp, WilsonGraphIncumbentCorrelationPublication.groupSeries g hg, ?_⟩
  intro P hP
  obtain ⟨determined, named⟩ := WilsonGraphIncumbentCorrelationPublication.onEveryPeriod.{u} g hg p hp
  have same := groupUnique.{u} g hg (WilsonGraphIncumbentCorrelationPublication.allRows.{u} g hg)
    (WilsonGraphIncumbentWardTestedGround.onGroup g hg) hP determined
  exact same.symm ▸ named

end YM.Integration.WilsonGraphNamedCorrelationEstimates
end

