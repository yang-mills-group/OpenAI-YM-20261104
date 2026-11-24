import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Estimates
import YM.Integration.WilsonGraphNamedCorrelationEstimates

set_option autoImplicit false

noncomputable section
namespace YangMills.CorrelationMatching.Construction

open Matching
open YM.Integration
open WilsonGraphPublishedReturnLaws

universe u

/-- The measured coupling and the field maps are those of the selected hierarchy. -/
def measurement {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}
    {T : Hierarchy C} (H : Matching.CorrelationOnly.Measurement B T) :
    CorrelationMatching.Measurement B T where
  coupling := H.clock
  frame := H.frame
  includeField := H.includeField
  positive := H.positive
  oneLoop := H.oneLoop
  nested := H.nested
  frameAxes := H.frameAxes
  unit := H.unit
  includeLabel := H.includeLabel
  includeInsertion := H.includeInsertion
  multilinear := H.multilinear

/-- On separated configurations the coefficient computed by the continuum graphs
agrees with the coefficient used to prove the Wilson estimates. -/
private theorem graphRead (g : GaugeGroup) :
    WilsonGraphWardExtensional.SeparatedRead
      (_root_.IssuedMaxwell.GraphCoefficients.issued g) (coefficientTable g) :=
  fun {n} k a x hx => WilsonGraphGroupPositionReference.agreement g n k a x hx

theorem graphEstimates (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (strict : StrictMono periods) :
    Estimates g (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
      (measurement (measurementOnPick.{u} g hg periods strict)) := by
  let S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
  let H := measurementOnPick.{u} g hg periods strict
  have h := WilsonGraphNamedCorrelationEstimates.atPeriods.{u} g hg periods strict
  have forward : WilsonGraphWardExtensional.SeparatedRead
      (_root_.IssuedMaxwell.GraphCoefficients.issued g) (coefficientTable g) :=
    fun k a x hx => graphRead g k a x hx
  have backward : WilsonGraphWardExtensional.SeparatedRead (coefficientTable g)
      (_root_.IssuedMaxwell.GraphCoefficients.issued g) := fun k a x hx => (forward k a x hx).symm
  have bounds := Matching.CorrelationOnly.filedCorrelationsOnSeparated S H forward
    (Matching.CorrelationOnly.groupFiledCorrelationsOfShape _ S H h.jets)
  refine ⟨fun n d => ⟨0, bounds.tested n d⟩, bounds.compact, bounds.jets, h.phases, ?_, ?_⟩
  · obtain ⟨P, hP, unique⟩ := h.wardIndependent
    refine ⟨P, WilsonGraphWardExtensional.determined forward S P hP, ?_⟩
    intro Q hQ
    exact unique Q (WilsonGraphWardExtensional.determined backward S Q hQ)
  · intro P hP
    exact h.wardNamed P (WilsonGraphWardExtensional.determined backward S P hP)

end YangMills.CorrelationMatching.Construction
end
