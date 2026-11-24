import YM.Integration.WilsonThermometerUnitFilingPaidBlend
import YM.Integration.WilsonCapturedPrimaryNamedReturn

/-! Each genuine face of the returned Wilson thermometer in the one rooted reflected chamber. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingNamedFaces
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonReflectedPhysicalFiling (Arms reading)
open WilsonThermometerOwnOffsetField OPE.Cards
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
variable (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
open RG12 OPE.Therm WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake
open WilsonThermometerUnitFilingFeed WilsonCapturedPrimaryNamedReturn
open private constant_field from YM.Integration.WilsonThermometerUnitFilingReflected
local notation "C" => R.family
abbrev grades (i:Fin 3):ℕ:=(grade i).val
def columns (A:Group R.family 6) (z:UVIndex) (s:Finset (Fin 3)) (i:Fin 3):(C).label (grades i):=
  A.station.wheel.atCut z (index A (grade i)) (vector A s i)
local notation "pos" y:max ax:max => WilsonCapturedPrimaryPhysicalArray.registered y (some ax)

include simple in
theorem returned_at {N p u:ℕ} (door:Opened C 0 u p) (un:u≤N) (Y:Cut C N p):
    WilsonCapturedPrimaryScaledCounter.difference R door un Y=Y-report R Y u • (1:Cut C N p):=by
  rw [WilsonCapturedPrimaryScaledCounter.difference,constant_field R simple (door.post.trans un)]
  simp only [report,dif_pos (And.intro door un),WilsonMacroscopicRichChildRegistration.returned]

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v J u:ℕ) (wide:4<v) (enlarged:(C).ref 0≤J) (station:∀p,Opened C 0 u p)
    (tiling:Stock.Tabs.opens (C).path.levels 1 J u) (φ:Test 3) :
    ∃K:ℝ,1≤K ∧ ∀ᶠ radius in trail,
    let m:=capture R radius
    let k:=launch R simple v radius
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (z:Fin 3→Site ((C).side N p)),
      WilsonSeparatedOriginalThermometerCells.weight φ
        (WilsonSeparatedOriginalThermometerCells.positions (R:=R) radius (N,p)) z≠0 →∀ax:Fin 3,
      ∃(V:(i:Fin 3)→Sight C (grades i) p) (sec:(i:Fin 3)→Emblems C (grades i)),
      WilsonCapturedPrimaryFiledArms.entered R grades (pos z ax) (k:=k) V sec ∧
      ∀(A:Group R.family 6) (s:Finset (Fin 3)) (w:(i:Fin 3)→Palette C (grades i)),
      primary R (p:=p) grades sec kn.le (columns R A (N,p) s) w →
      let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
      let Y:Cut C N p:=placed R A (N,p) s (pos z ax)
      Booked C N p 0 Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
        (WilsonCapturedPrimaryFiledArms.rent R grades w*(K*radius^(1/32:ℝ))) (Y-report R Y u • (1:Cut C N p)):=by
  obtain ⟨K,gain,dated⟩:=WilsonCapturedPrimaryNamedReturn.original R simple book shop slow 6 v 0 J u wide enlarged
    station tiling φ grades (fun i=>Nat.le_of_lt_succ (grade i).isLt)
  refine ⟨K,gain,?_⟩
  filter_upwards [dated] with radius quote
  obtain ⟨um,mk,panels⟩:=quote
  refine ⟨um,mk,?_⟩;intro N p kn z active ax
  rw [WilsonCapturedPrimaryCenteredMeter.charged] at active
  obtain ⟨V,sec,hit,rooms⟩:=panels N p kn z active ax
  refine ⟨V,sec,hit,?_⟩;intro A s w born
  have result:=rooms (columns R A (N,p) s) w born
  change Booked C N p 0 _ u _ ∧ PaidAt (C).S N p J ((C).beta N p) _ (WilsonCapturedPrimaryScaledCounter.difference R _ _ _) at result
  rw [returned_at R simple] at result
  have same:WilsonCapturedPrimaryNamedReturn.field R grades (columns R A (N,p) s) (pos z ax)=
      WilsonThermometerCourseIntake.placed R A (N,p) s (pos z ax):=rfl
  rw [same] at result
  simpa only [Nat.cast_zero,zero_add] using result

end YM.Integration.WilsonThermometerUnitFilingNamedFaces
