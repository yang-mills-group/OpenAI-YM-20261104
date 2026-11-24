import YM.Integration.WilsonThermometerUnitFilingNamedFaces
import YM.Integration.WilsonThermometerNominatedProperStop

/-! The spatial appointment for an absolute detector cell, requiring the named lifted faces that occur in its inverse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedReflectionArms
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
open WilsonThermometerUnitFilingNamedFaces WilsonThermometerNominatedFaceCylinder
local notation "C" => R.family
open WilsonThermometerAlignedCells WilsonThermometerFiniteConnectedCells WilsonGeometricSignedCapture Marker FVA1
open WilsonCapturedPrimaryNamedReturn WilsonCapturedPrimaryFiledArms
local notation "J₃" => Stock.census (Fin 3)
local notation "home" x:max => atOrigin (offsets x)
local notation "trueField" A:max N:max p:max s:max o:max =>
  WilsonThermometerCourseIntake.placed R A (N,p) (s).val (o).origin

private theorem centered {N p:ℕ} (x:Fin 3→Site ((C).side N p)) :
    WilsonCapturedPrimaryPhysicalArray.registered x (some (0:Fin 3))=home x:=by
  funext v; fin_cases v <;> simp [WilsonCapturedPrimaryPhysicalArray.registered,atOrigin,offsets]

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v J u:ℕ) (ju:J≤u) (wide:4<v) (enlarged:(C).ref 0≤J) (station:∀p,Opened C 0 u p)
    (tiling:Stock.Tabs.opens (C).path.levels 1 J u) (φ:Test 3) :
    ∃K:ℝ,1≤K ∧ ∀ᶠ r in trail,
    let m:=capture R r
    let k:=launch R simple v r
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (x:Fin 3→Site ((C).side N p)),
      WilsonSeparatedOriginalThermometerCells.weight φ
        (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)) x≠0 →
      ∃(V:(j:Fin 3)→Sight C (grades j) p) (sec:(j:Fin 3)→Emblems C (grades j)),
      entered R grades (home x) (k:=k) V sec ∧
      ∀(A:Group R.family 6) (o:FVA1.Positions (Fin 3) ((C).side N p)), o.origin=home x →
      ∀(_:∀v:Fin 3,R.family.ref (grade v).val≤N) (c:(J₃).Mode→ℂ)
        (w:(J₃).Mode→(j:Fin 3)→Palette C (grades j)),
      (∀s,c s≠0→primary R (p:=p) grades sec kn.le (columns R A (N,p) s.val) (w s)) →
      let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
      let fare:=fun s=>rent R grades (w s)*(K*r^(1/32:ℝ))
      let Y:=WilsonThermometerNominatedFaceCylinder.source R A o c
      (∀s,c s≠0→
        Booked C N p 0 (trueField A N p s o) u un ∧
        PaidAt (C).S N p J ((C).beta N p) (fare s)
          ((trueField A N p s o)-report R (trueField A N p s o) u • (1:Cut C N p))) ∧
      Booked C N p 0 Y u un ∧
      ‖take c (measured R A (N,p) x)-report R Y u‖≤
        (∑s,‖c s‖*rent R grades (w s))*(K*r^(1/32:ℝ)):=by
  obtain ⟨K,good,late⟩:=WilsonThermometerUnitFilingNamedFaces.original R simple book shop slow v J u
    wide enlarged station tiling φ
  refine ⟨K,good,late.mono ?_⟩
  intro r ready;obtain ⟨um,mk,room⟩:=ready
  refine ⟨um,mk,?_⟩
  intro N p kn x alive
  obtain ⟨V,sec,entry,earns⟩:=room N p kn x alive (0:Fin 3)
  rw [centered R x] at entry earns
  refine ⟨V,sec,entry,?_⟩
  intro A o hits refs c w bought un fare Y
  have arms (s:(J₃).Mode) (positive:c s≠0) :=earns A s.val (w s) (bought s positive)
  rw [←hits] at arms
  refine ⟨arms,?_⟩
  obtain ⟨booked,observed⟩:=WilsonThermometerNominatedFaceCylinder.heard R A simple o c ju
    (le_refl u) un (station p) fare arms
  refine ⟨booked,?_⟩
  rw [hits,←WilsonThermometerRegisteredAncestralProperTest.translated_table R A refs x] at observed
  simpa only [Finset.sum_mul,mul_assoc,fare] using observed

end YM.Integration.WilsonThermometerNominatedReflectionArms
