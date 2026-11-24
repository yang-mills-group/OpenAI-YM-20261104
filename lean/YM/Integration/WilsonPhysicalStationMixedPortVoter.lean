import YM.Integration.WilsonPhysicalStationMixedCommittedBallot
import YM.Integration.WilsonPhysicalStationPureBorn
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedPortVoter
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price
open Further.CorrectedLift (ladder)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonPhysicalStationFullVote (Head Below)
open WilsonPhysicalStationPureReceipt (coefficients ballot left)
open WilsonPhysicalStationMixedListener (port value actual)
open WilsonPhysicalStationThermalStart (entered)
variable {G:Gauge}(R:Run G){S:Table R.family.book}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){h k:ℕ}(q:ℕ)
local notation "C₀"=>Cells.standard R.family
local notation "F₀"=>R.family.labels.level h
def filed (u:(C₀).Field h):(C₀).Field h:=(J₀ (V k).wheel.r h).symm (J.U k h u)
def Pure (u:(C₀).Field h):Prop:=∀a:(F₀).Index,ladder R.family h u a≠0→(F₀).grades a=(h,q)
theorem original (u:(C₀).Field h)(pure:Pure R q u):
    ballot R J₀ J V (k:=k) q (filed R J₀ J V (k:=k) u)=u:=by
  unfold filed ballot
  simp only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  have letters:ladder R.family h (WilsonPhysicalStationGradedVoter.portion R.family h (·=(h,q)) u)=ladder R.family h u:=by
    funext a
    rw [WilsonPhysicalStationGradedVoter.tally]
    split_ifs with yes
    · rfl
    · exact (not_ne_iff.mp (fun live=>yes (pure a live))).symm
  simpa only [Further.CorrectedLift.ladder_reads] using congrArg ((C₀).project h) letters

theorem coordinates (u:(C₀).Field h)(pure:Pure R q u)(a:Head R.family h):
    coefficients R J₀ J V (k:=k) q (filed R J₀ J V (k:=k) u) a=ladder R.family h u a.val:=by
  unfold coefficients
  rw [original R J₀ J V q u pure]

theorem named (a:Head R.family h):
    Pure R ((F₀).grades a.val).2 (WilsonPhysicalVaneBasis.field R.family h a.val):=by
  intro i live
  rw [WilsonPhysicalVaneBasis.pure R.family h a.val i live]
  exact Prod.ext a.property rfl

end YM.Integration.WilsonPhysicalStationMixedPortVoter
end
