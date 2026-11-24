import YM.Integration.WilsonPhysicalStationMixedWickCapBook
import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerGradedReading

/-! The measured position change on the actual original cap file, with the full untouched cutoff
label for every entry of a finite determining or target roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPositionedCap
open Function Set Filter Spec Trace Trace.Over MergeProof.East Table Extraction PhysMS PhysMS.Frame Trace.Pilot Lattice Wilson
open PhysicalNext.Repeat.Legato RG RG17 Source FullVolume Next.UVStress Climb OPE Maxwell XSpace XSpace.Normalize
open GapsContact GapsContact.Ascent WilsonPositionThermometerCapStation WilsonThermometerUnitFilingFourSquare
open WilsonPositionCapTransport (through)
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→tower S)(Z:Store G){D:ℕ}{l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z

theorem aligned (lead:Leading F J):localCost trail J (posed):=by
  intro d v
  apply (WilsonPositionPrescribedLeading.applied F J Z lead d v).congr
  intro r
  change WilsonPositionPrescribedFrame.change F J Z d r v=(J r d).symm ((J r d) (WilsonPositionPrescribedFrame.change F J Z d r v))
  rw [LinearEquiv.symm_apply_apply]

def digit (A:ℝ→Group C D)(r:ℝ)(j:Fin (D+1))(v:RG17.Free C j):RG17.Free C j:=
  (A r).change j (WilsonPositionPrescribedFrame.change F J Z j r v)

theorem written (A:ℝ→Group C D)(r:ℝ)(j:Fin (D+1))(v:RG17.Free C j):
    (through J (posed) A r).change j v=digit F J Z A r j v:=by
  change (A r).change j ((J r j).symm ((J r j) (WilsonPositionPrescribedFrame.change F J Z j r v)))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem bounded (A:ℝ→Group C D)(paid:WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J)
    (lead:Leading F J)(j:Fin (D+1))(v:RG17.Free C j):
    Tendsto (fun r=>digit F J Z A r j v) trail (𝓝 v):=
  (WilsonPositionCapTransport.near J (posed) A paid (aligned F J Z lead) j v).congr fun r=>written F J Z A r j v

open private lift_entry from YM.Integration.WilsonPositionThermometerGradedReading in
theorem original (A:ℝ→Group C D)(paid:WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J):
    ∀ᶠr in trail,∀(j:Fin (D+1))(v:RG17.Free C j),
      ∃arm:Arm C S (l:Filter _) j (posed r j v),
        arm.source=(fun uv=>(A r).station.wheel.atCut uv (index (A r) j) (digit F J Z A r j v)) ∧
        arm.label=(A r).lift (index (A r) j) (digit F J Z A r j v):=by
  filter_upwards [paid 0] with r archive j v
  let bill:=digit F J Z A r j v
  have lands:=lift_entry (index (A r) j) bill archive.2.2.2.1
  have filed:=((archive.2.2.2.2.1 j).2.2 (WilsonPositionPrescribedFrame.change F J Z j r v)).symm
  exact ⟨⟨_,_,lands,filed⟩,rfl,rfl⟩

end YM.Integration.WilsonPhysicalStationMixedWickPositionedCap
end
