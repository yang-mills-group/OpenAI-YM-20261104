import YM.Integration.WilsonPhysicalStationMixedWickPositionedCap
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalRose
import YM.Integration.WilsonPhysicalStationMixedWickPositionedSites
import YM.Integration.WilsonPositionScaleLawGuardUnit
import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerGradedReading

/-! The measured position change on the actual original cap file, with the full untouched cutoff
label for every entry of a finite determining or target roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPositionedMeter
open Function Set Filter Spec Trace Trace.Over MergeProof.East Table Extraction PhysMS PhysMS.Frame Trace.Pilot Lattice Wilson
open PhysicalNext.Repeat.Legato RG RG17 Source FullVolume Next.UVStress Climb OPE Maxwell XSpace XSpace.Normalize
open GapsContact GapsContact.Ascent WilsonPositionThermometerCapStation WilsonThermometerUnitFilingFourSquare
open WilsonPositionCapTransport (through)
open WilsonPositionProgramTrialPublicJointPivotOriginalArms WilsonPositionCapTransport
open WilsonPositionProgramTrialPublicJointPivotEvidence (old atHome)
open WilsonPositionProgramTrialPublicJointPivotOriginalRose (signed)
open WilsonPositionThermometerConnected (value)
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){D n:ℕ}{l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z.store

def moved (d:ℕ)(r:ℝ)(v:Sec G d):Sec G d:=
  WilsonPhysicalStationMixedWickPositionedSites.field F J Z.store r d ((Maxwell.Free.fields R.family.labels d).symm v)

theorem unit (d:ℕ)(r:ℝ):moved F J Z d r (leaf G d)=leaf G d:=by
  have atom:(Maxwell.Free.fields R.family.labels d).symm (leaf G d)=(Bel R.family.book).unit d:=by
    apply (Maxwell.Free.fields R.family.labels d).injective
    rw [LinearEquiv.apply_symm_apply,WilsonPositionScaleLawGuardUnit.named]
  unfold moved WilsonPhysicalStationMixedWickPositionedSites.field
  rw [atom,WilsonPositionScaleLawGuardUnit.positioned,WilsonPositionScaleLawGuardUnit.named]

theorem missing (d:ℕ)(r:ℝ)(p:Fin 3→Sec G d)(s:Finset (Fin 3))(i:Fin 3):
    Rose.missing (fun j=>moved F J Z d r (p j)) s i=moved F J Z d r (Rose.missing p s i):=by
  by_cases held:i∈s <;> simp [Rose.missing,held,unit]

theorem report (d:ℕ)(r:ℝ)(rp:0<r)(p:Fin 3→Sec G d)(φ:Test 3):
    old F J d φ rp (fun j=>moved F J Z d r (p j))=old F (posed) d φ rp p:=by
  change φ.applyTo _=φ.applyTo _
  apply congrArg φ.applyTo
  funext x
  apply congrArg WilsonPositionThermometerConnected.value
  funext s
  change S.classMoment (spectator F none) _ (r • x) _=S.classMoment (spectator F none) _ (r • x) _
  apply congrArg
  funext i
  rw [missing]
  change J r d ((Maxwell.Free.fields R.family.labels d).symm
    ((Maxwell.Free.fields R.family.labels d) (WilsonPositionPrescribedFrame.change F J Z.store d r _)))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem original (simple:G.Simple)(prior:(l:Filter _)≤f.fuse)(A:ℝ→Group C D)
    (paid:Book (f:=f) (l:=l) (H:=H) A J):
    ∀ᶠr in trail,∀rp:0<r,∀(d:Fin (D+1))(p:Fin 3→Sec G d)(φ:Test 3),
      Tendsto (signed (A r) d (fun i=>moved F J Z d r (p i)) φ r) (l:Filter _) (𝓝 (old F (posed) d φ rp p)):=by
  filter_upwards [paid 0] with r ready rp d p φ
  rw [←report F J Z d r rp p φ]
  exact WilsonPositionProgramTrialPublicJointPivotOriginalRose.original F J simple prior rp (A r) ready d _ φ

theorem thermometer (simple:G.Simple)(prior:(l:Filter _)≤f.fuse)(A:ℝ→Group C 6)
    (paid:Book (f:=f) (l:=l) (H:=H) A J):
    ∀ᶠr in trail,0<r→Tendsto
      (fun z=>(signed (A r) (6:Fin 7) (fun i=>moved F J Z 6 r (Rose.tag G i)) (Rose.test Z.criterion) r z).re)
      (l:Filter _) (𝓝 ((Rose.cT Z.criterion.cut G Z.criterion.image)*WilsonPositionHomogeneousFrame.reading F J Z r)):=by
  filter_upwards [original F J Z simple prior A paid] with r filed rp
  have sale:=filed rp (6:Fin 7) (Rose.tag G) (Rose.test Z.criterion)
  rw [WilsonPositionThermometerReading.calibrated_denominator]
  exact Complex.continuous_re.continuousAt.tendsto.comp sale

end YM.Integration.WilsonPhysicalStationMixedWickPositionedMeter
end
