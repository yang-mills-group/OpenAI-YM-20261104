import YM.Integration.WilsonThermometerUnitFilingRelativeChamber
import YM.Integration.WilsonThermometerUnitFilingNamedFaces
import YM.Integration.WilsonCapturedPrimaryStationArms

/-! At each funded radius, spend the original occupied arm fees only at one charged actual tuple
for every nonvanishing relative cell of the reached programme. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRelativeStation
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper PhysMS
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerGradedReading (vector)
open WilsonCapturedPrimaryFaceWallet WilsonCapturedPrimaryActiveArms
open OPE.Cards XSpace XSpace.Normalize XSpace.Rose
open Table Spec Climb Next.UVStress RG12 RG17
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "origin" z:max ax:max => WilsonCapturedPrimaryPhysicalArray.registered z (some ax)

private abbrev height (i:Fin 3):ℕ:=WilsonCapturedPrimaryStationArms.height i

open WilsonCapturedPrimaryStationArms (nominees)
open WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingReflectedShape (Key tariff)
open scoped Classical BigOperators

open WilsonThermometerUnitFilingRelative (Grid)
open WilsonThermometerAlignedCells (placedAt atOrigin mass)
open Next.UVStress OPE.Cards
local notation "J₃" => Stock.census (Fin 3)
local notation "site!" z:max c:max => (WilsonThermometerRegisteredCells.placement (R:=R) z (c).val).origin

private theorem carrier {N p:ℕ} (r:ℝ) (φ:Test 3) (c:Grid R (N,p) r φ):
    ∃a:Site ((C).side N p),WilsonCenteredCompactBooking.mass R φ r (N,p) (placedAt c.val a)≠0:=by
  by_contra none
  push Not at none
  apply c.property
  unfold WilsonThermometerAlignedCells.mass
  apply Finset.sum_eq_zero;intro a _
  rw [WilsonCapturedPrimaryCenteredMeter.charged]
  exact none a

private theorem anchored {N p:ℕ} (r:ℝ) (φ:Test 3) (c:Grid R (N,p) r φ) (a:Site ((C).side N p)):
    WilsonCapturedPrimaryPhysicalArray.registered (placedAt c.val a) (some (0:Fin 3))=site! (N,p) c:=by
  funext i;fin_cases i <;> simp [WilsonCapturedPrimaryPhysicalArray.registered,WilsonThermometerRegisteredCells.placement,
    placedAt,atOrigin]

def host {N p:ℕ} (r:ℝ) (φ:Test 3) (c:Grid R (N,p) r φ):Fin 3→Site ((C).side N p):=
  WilsonCapturedPrimaryPhysicalArray.registered (placedAt c.val (carrier R r φ c).choose) (some 0)

def rent {N p:ℕ} (r K:ℝ) (φ:Test 3) (Q:Grid R (N,p) r φ→Poly J₃)
    (y:∀(_:Grid R (N,p) r φ) (s:(J₃).Mode) (i:Fin 3),Palette C (level height s.val i)):ℝ:=
  ∑(c:Grid R (N,p) r φ)(s:(J₃).Mode),‖mass (R:=R) r (N,p) φ c.val*wallet (Q c) s‖*
    (((∏ i ∈ s.val, (1+size (y c s i)))*2^(3-s.val.card))*(K*r^(1/32:ℝ)))

include simple in
theorem original (book:OPE.Package C R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v J u:ℕ) (wide:4<v) (enlarged:(C).ref 0≤J) (ju:J≤u) (station:∀p,Opened C 0 u p)
    (tiling:Stock.Tabs.opens (C).path.levels 1 J u) (φ:Test 3) :
    ∃ K:ℝ,1≤K ∧ ∀ᶠ r in trail,
    let m:=capture R r
    let k:=launch R simple v r
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn:k<N),
      ∃ good:∀c:Grid R (N,p) r φ,Shelf (N:=N) (p:=p) R k height (host R r φ c),
      ∀(f:Extraction.Order) (H:(Bel (C).book).Hierarchy) (A:Group C 6),
       A.station.checked f H A.horizon →
       (∀ t:Fin 7,A.change t ((Bel (C).book).unit t)=(Bel (C).book).unit t) →
       A.station.k<N → (∀i,(C).ref (height i)≤N) →
       ∀(Q:Grid R (N,p) r φ→Poly J₃)
         (y:∀(_:Grid R (N,p) r φ) (s:(J₃).Mode) (i:Fin 3),Palette C (level height s.val i)),
       (∀ (c:Grid R (N,p) r φ) (s:(J₃).Mode),
        WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level height s.val) ((good c).paths s.val) kn.le
          (WilsonCapturedPrimaryFaceWallet.label R s.val (nominees R A (N,p))) (y c s)) →
       let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
       let Y:=WilsonThermometerUnitFilingRelative.source R A (N,p) r φ Q
       let bill:=rent R r K φ Q y
       Booked C N p 0 Y u un ∧ PaidAt (C).S N p J ((C).beta N p) bill (Y-report R Y u • (1:Cut C N p)) ∧
         ‖tested R A (N,p) r φ (WilsonThermometerUnitFilingRelative.table R (N,p) r φ Q)-report R Y u‖≤bill:=by
  classical
  obtain ⟨K,positive,post⟩:=WilsonCapturedPrimaryStationArms.original R simple book shop slow v 0 J u
    wide enlarged station tiling φ
  refine ⟨K,positive,?_⟩
  filter_upwards [post] with r bill
  obtain ⟨um,mk,raw⟩:=bill
  refine ⟨um,mk,?_⟩;intro N p kn
  let a(c:Grid R (N,p) r φ):=(carrier R r φ c).choose
  have issue(c:Grid R (N,p) r φ):=raw N p kn (placedAt c.val (a c)) (carrier R r φ c).choose_spec (0:Fin 3)
  choose good returns using issue
  refine ⟨good,?_⟩;intro f H A cal unit late starts Q y fitted
  let fee(c:Grid R (N,p) r φ) (s:(J₃).Mode):=
    ((∏i∈s.val,(1+size (y c s i)))*2^(3-s.val.card))*(K*r^(1/32:ℝ))
  apply WilsonThermometerUnitFilingRelativeChamber.original R simple A (N,p) r φ Q starts ju um
    ((capture R r).le_succ.trans (mk.le.trans kn.le)) (station p) fee
  intro c s _
  have paid:=returns c f H A cal unit late starts s.val (y c s) (fitted c s)
  dsimp only [] at paid
  rw [WilsonThermometerUnitFilingNamedFaces.returned_at R simple,anchored R r φ c (a c)] at paid
  simpa only [fee,Nat.cast_zero,zero_add] using paid

end YM.Integration.WilsonThermometerUnitFilingRelativeStation
