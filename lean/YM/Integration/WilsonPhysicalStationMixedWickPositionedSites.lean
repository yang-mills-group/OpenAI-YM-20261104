import YM.Integration.WilsonPhysicalStationMixedWickPositionedCap
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalArms
import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerGradedReading

/-! The measured position change on the actual original cap file, with the full untouched cutoff
label for every entry of a finite determining or target roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPositionedSites
open Function Set Filter Spec Trace Trace.Over MergeProof.East Table Extraction PhysMS PhysMS.Frame Trace.Pilot Lattice Wilson
open PhysicalNext.Repeat.Legato RG RG17 Source FullVolume Next.UVStress Climb OPE Maxwell XSpace XSpace.Normalize
open GapsContact GapsContact.Ascent WilsonPositionThermometerCapStation WilsonThermometerUnitFilingFourSquare
open WilsonPositionCapTransport (through)
open WilsonPositionProgramTrialPublicJointPivotOriginalArms WilsonPositionCapTransport
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→tower S)(Z:Store G){D n:ℕ}{l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z

def field (r:ℝ)(d:ℕ)(v:RG17.Free C d):Sec G d:=
  Maxwell.Free.fields R.family.labels d (WilsonPositionPrescribedFrame.change F J Z d r v)

theorem src (A:Group C D)(r:ℝ)(j:Fin (D+1))(v:RG17.Free C j)(z:ℕ×ℕ):
    source A j (field F J Z r j v) z=A.station.wheel.atCut z (index A j)
      (WilsonPhysicalStationMixedWickPositionedCap.digit F J Z (fun _=>A) r j v):=by
  simp only [source,field,LinearEquiv.symm_apply_apply,WilsonPhysicalStationMixedWickPositionedCap.digit]

theorem cutoff (simple:G.Simple)(prior:(l:Filter _)≤f.fuse)(A:ℝ→Group C D)
    (paid:Book (f:=f) (l:=l) (H:=H) A J):
    ∀ᶠr in trail,0<r→∀(j:Fin n→Fin (D+1))(v:(i:Fin n)→RG17.Free C (j i))
      (K:Set (Points n)),IsCompact K→K⊆conf n→∀e:ℝ,0<e→
      ∀ᶠz:ℕ×ℕ in (l:Filter _),∀x∈K,‖raw (A r) j (fun i=>field F J Z r (j i) (v i)) r z x-
        PhysMS.measured F none (posed r) (d:=fun i=>(j i).val) v r x‖<e:=by
  filter_upwards [paid 0] with r ready pos j v K compact sep e ep
  have earn:=WilsonPositionProgramTrialPublicJointPivotOriginalArms.cutoff F J simple prior pos (A r) ready j
    (fun i=>field F J Z r (j i) (v i)) compact sep ep
  simpa only [field,LinearEquiv.symm_apply_apply,PhysMS.measured,WilsonPositionPrescribedFrame.positioned,
    LinearEquiv.trans_apply] using earn

theorem original (prior:(l:Filter _)≤f.fuse)(A:ℝ→Group C D)
    (paid:Book (f:=f) (l:=l) (H:=H) A J):
    ∀ᶠr in trail,∀pos:0<r,∀(j:Fin n→Fin (D+1))(v:(i:Fin n)→RG17.Free C (j i))(φ:Test n),
      Tendsto (ordinary (A r) j (fun i=>field F J Z r (j i) (v i)) pos φ) (l:Filter _)
        (𝓝 (φ.applyTo (fun x=>PhysMS.measured F none (posed r) (d:=fun i=>(j i).val) v r x))):=by
  filter_upwards [paid 0] with r ready pos j v φ
  have earn:=WilsonPositionProgramTrialPublicJointPivotOriginalArms.measured F J prior pos (A r) ready j
    (fun i=>field F J Z r (j i) (v i)) φ
  simpa only [field,LinearEquiv.symm_apply_apply,PhysMS.measured,WilsonPositionPrescribedFrame.positioned,
    LinearEquiv.trans_apply] using earn

end YM.Integration.WilsonPhysicalStationMixedWickPositionedSites
end
