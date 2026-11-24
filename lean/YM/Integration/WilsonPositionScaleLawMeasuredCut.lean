import YM.Integration.WilsonPositionScaleLawMeasuredOriginal
import YM.Integration.WilsonPhysicalStationMixedWickPositionedMeter
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredCut
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionProgramTrialPublicJointPivotOriginalArms (ordinary)
open WilsonPhysicalStationMixedWickPositionedMeter (moved)
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S)(J:ℝ→tower S) (Z:WilsonPrescription G)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{B n:ℕ}
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z.store
def sample (A:Group R.family B)(j:Fin (B+1)) {r:ℝ} (rp:0<r)(φ:Test n)(v:Fin n→Sec G j) :=
  ordinary A (fun _:Fin n=>j) (fun i=>moved F J Z j r (v i)) rp φ
theorem receives (prior:(l:Filter _)≤o.fuse) (A:ℝ→Group R.family B)
    (paid:Book (f:=o) (l:=l) (H:=H) A J) :
    ∀ᶠr in trail,∀rp:0<r,∀j:Fin (B+1),∀m:ℕ,∀φ:Test m,∀v:Fin m→Sec G j,
      Tendsto (sample F J Z (A r) j rp φ v) (l:Filter _) (𝓝 (WilsonPositionPrescribedScreen.hierarchy F posed j r m φ v)) := by
  filter_upwards [paid 0] with r ready rp j m φ v
  rw [WilsonPositionPrescribedScreen.actual F posed j m φ v rp]
  have fee:=WilsonPositionProgramTrialPublicJointPivotOriginalArms.measured F J prior rp (A r) ready
    (fun _:Fin m=>j) (fun i=>moved F J Z j r (v i)) φ
  simpa only [sample,moved,WilsonPhysicalStationMixedWickPositionedSites.field,LinearEquiv.symm_apply_apply,
    PhysMS.measured,WilsonPositionPrescribedFrame.positioned,LinearEquiv.trans_apply] using fee
def bag (A:Group R.family B)(j:Fin (B+1)) {r:ℝ}(rp:0<r)(z:ℕ×ℕ) : (Z.store.survey j).Bag :=
  fun i a=>sample F J Z A j rp (((Z.store.survey j).scope i).t) (fun s=>Module.finBasis ℝ (Sec G j) (a s)) z
theorem menu (prior:(l:Filter _)≤o.fuse) (A:ℝ→Group R.family B)
    (paid:Book (f:=o) (l:=l) (H:=H) A J) :
    ∀ᶠr in trail,∀rp:0<r,∀j:Fin (B+1),
      Tendsto (bag F J Z (A r) j rp) (l:Filter _) (𝓝 ((Z.store.survey j).purse (WilsonPositionPrescribedScreen.hierarchy F posed j r))) := by
  filter_upwards [receives F J Z prior A paid] with r given rp j
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro a
  exact given rp j _ _ _
def reading (A:Group R.family B)(within:6≤B) (r:ℝ)(z:ℕ×ℕ) : ℝ :=
  (WilsonPositionProgramTrialPublicJointPivotOriginalRose.signed A ⟨6,by omega⟩ (fun i=>moved F J Z 6 r (Rose.tag G i)) (Rose.test Z.criterion) r z).re / Rose.cT Z.criterion.cut G Z.criterion.image
theorem sensor (simple:G.Simple) (prior:(l:Filter _)≤o.fuse)(A:ℝ→Group R.family B)
    (paid:Book (f:=o) (l:=l) (H:=H) A J) (within:6≤B) :
    ∀ᶠr in trail,0<r→Tendsto (reading F J Z (A r) within r) (l:Filter _) (𝓝 (WilsonPositionHomogeneousFrame.reading F J Z r)) := by
  filter_upwards [WilsonPhysicalStationMixedWickPositionedMeter.original F J Z simple prior A paid] with r filed rp
  have fee:=filed rp ⟨6,by omega⟩ (Rose.tag G) (Rose.test Z.criterion)
  let c:=Rose.cT Z.criterion.cut G Z.criterion.image
  have got : Tendsto (fun z=>(WilsonPositionProgramTrialPublicJointPivotOriginalRose.signed (A r) ⟨6,by omega⟩ (fun i=>moved F J Z 6 r (Rose.tag G i)) (Rose.test Z.criterion) r z).re)
      (l:Filter _) (𝓝 (c*WilsonPositionHomogeneousFrame.reading F J Z r)) := by
    rw [WilsonPositionThermometerReading.calibrated_denominator]
    exact Complex.continuous_re.continuousAt.tendsto.comp fee
  unfold reading
  simpa [c,Z.criterion.fresh.ne] using! got.div_const c
end YM.Integration.WilsonPositionScaleLawMeasuredCut
