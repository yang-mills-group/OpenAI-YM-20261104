import YM.Integration.WilsonThermometerNominatedReflectionArms

/-! Reflected proper and full cutoff sources on the original fitted stage, purchased at their actual inverse coordinates for every nonvanishing physical test cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredReflection
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

def own {N p k:ℕ} (A:Group R.family 6) (sec:(j:Fin 3)→Emblems C (grades j)) (kn:k≤N) (s:(J₃).Mode) :
    (j:Fin 3)→Palette C (grades j):=
  fun j=>WilsonNeutralOffsetCutoff.input R (p:=p) (sec j) kn (columns R A (N,p) s.val j)

def Issued (φ:Test 3) (K r:ℝ) {k u N:ℕ} (J p:ℕ) (un:u≤N) (kn:k≤N):Prop:=
  ∀(x:Fin 3→Site ((C).side N p)), WilsonSeparatedOriginalThermometerCells.weight φ
    (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)) x≠0 →
    ∃(V:(j:Fin 3)→Sight C (grades j) p) (sec:(j:Fin 3)→Emblems C (grades j)),
      entered R grades (home x) (k:=k) V sec ∧
      ∀(A:Group R.family 6) (o:FVA1.Positions (Fin 3) ((C).side N p)),o.origin=home x →
      ∀(_:∀v:Fin 3,R.family.ref (grade v).val≤N) (s:(J₃).Mode),
        Booked C N p 0 (trueField A N p s o) u un ∧
        PaidAt (C).S N p J ((C).beta N p) (rent R grades (own R (p:=p) A sec kn s)*(K*r^(1/32:ℝ)))
          ((trueField A N p s o)-report R (trueField A N p s o) u • (1:Cut C N p))

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v J u:ℕ) (ju:J≤u) (wide:4<v) (enlarged:(C).ref 0≤J) (station:∀p,Opened C 0 u p)
    (tiling:Stock.Tabs.opens (C).path.levels 1 J u) (φ:Test 3):
    ∃K:ℝ,1≤K ∧ ∀ᶠ r in trail,
    let m:=capture R r
    let k:=launch R simple v r
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N), Issued R φ K r J p (um.trans (m.le_succ.trans (mk.le.trans kn.le))) kn.le:=by
  obtain ⟨K,positive,late⟩:=WilsonThermometerNominatedReflectionArms.original R simple book shop slow v J u ju wide enlarged station tiling φ
  refine ⟨K,positive,late.mono ?_⟩
  intro r gate
  obtain ⟨um,mk,ready⟩:=gate
  refine ⟨um,mk,?_⟩
  intro N p kn x live
  obtain ⟨V,sec,entry,rows⟩:=ready N p kn x live
  refine ⟨V,sec,entry,?_⟩
  intro A o homeSame refs s
  have fire(t:(J₃).Mode):WilsonCapturedPrimaryNamedReturn.primary R (p:=p) grades sec kn.le (columns R A (N,p) t.val) (own R (p:=p) A sec kn.le t):=
    WilsonCapturedPrimaryNamedReturn.sparse R grades sec kn.le (columns R A (N,p) t.val)
  exact (rows A o homeSame refs (fun _=>1) (own R (p:=p) A sec kn.le) (fun t _=>fire t)).1 s one_ne_zero

end YM.Integration.WilsonThermometerRegisteredCenteredReflection
