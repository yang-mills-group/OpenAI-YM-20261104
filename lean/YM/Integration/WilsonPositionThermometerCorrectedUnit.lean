import YM.Integration.WilsonPositionPrescribedLift

/-! The same three corrected physical fields and the literal unit on all
seven cutoff faces of the original position thermometer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerCorrectedUnit
open Function Filter Set Finset Table Climb Trace Trace.Pilot Next.UVStress PhysMS
open Spec MergeProof.East Maxwell XSpace XSpace.Normalize XSpace.Rose
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy}

theorem corrected_unit (F : Final C f S) (J : ℝ → tower S) (W : Store G) (d : ℕ) (r : ℝ) :
    WilsonPositionPrescribedFrame.change F J W d r ((Bel C.book).unit d) = (Bel C.book).unit d := by
  let u := (Maxwell.Free.fields C.labels d).symm (leaf G d)
  have same : u=(Bel C.book).unit d := by
    apply Maxwell.Free.address_inj C.labels d
    rw [Maxwell.Free.unit_address]
    change ((Maxwell.Free.fields C.labels d) ((Maxwell.Free.fields C.labels d).symm (leaf G d))).1=_
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [← same]
  by_cases h : Bijective (stand (WilsonPositionPrescribedScreen.correction F J W d r))
  · exact (WilsonPositionPrescribedFrame.leg F J W h (leaf G d)).trans
      (congrArg (Maxwell.Free.fields C.labels d).symm (solitary _))
  · simp [WilsonPositionPrescribedFrame.change,h]

end YM.Integration.WilsonPositionThermometerCorrectedUnit
end
