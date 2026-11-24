import YM.Integration.WilsonThermometerUnitFilingRelativeStation

/-! The originally funded live reflected arms and their actual primary lift at every earned cell. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingReflectionBank
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

local notation "dims" => WilsonCapturedPrimaryStationArms.height

open WilsonCapturedPrimaryStationArms (nominees)
open WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingReflectedShape (Key tariff)
open scoped Classical BigOperators

open WilsonThermometerUnitFilingRelative (Grid)
open WilsonThermometerAlignedCells (placedAt atOrigin mass)
open Next.UVStress OPE.Cards
local notation "J₃" => Stock.census (Fin 3)
local notation "site!" z:max c:max => (WilsonThermometerRegisteredCells.placement (R:=R) z (c).val).origin

abbrev lifts {N p:ℕ} (r:ℝ) (φ:Test 3):=
  Grid R (N,p) r φ → (s:(J₃).Mode) → (i:Fin 3) → Palette C (level dims s.val i)
structure Bank (N p u J:ℕ) (r K:ℝ) (φ:Test 3) where
  k:ℕ
  live:k<N
  un:u≤N
  stock:∀c:Grid R (N,p) r φ,Shelf (N:=N) (p:=p) R k dims (WilsonThermometerUnitFilingRelativeStation.host R r φ c)
  serves:∀(f:Extraction.Order) (H:(Bel (C).book).Hierarchy) (A:Group C 6),
    A.station.checked f H A.horizon →
    (∀ t:Fin 7,A.change t ((Bel (C).book).unit t)=(Bel (C).book).unit t) →
    A.station.k<N → (∀i,(C).ref (dims i)≤N) →
    ∀(Q:Grid R (N,p) r φ→Poly J₃) (y:lifts (N:=N) (p:=p) R r φ),
    (∀ (c:Grid R (N,p) r φ) (s:(J₃).Mode),
      WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level dims s.val) ((stock c).paths s.val) live.le
        (WilsonCapturedPrimaryFaceWallet.label R s.val (nominees R A (N,p))) (y c s)) →
    let Y:=WilsonThermometerUnitFilingRelative.source R A (N,p) r φ Q
    let expense:=WilsonThermometerUnitFilingRelativeStation.rent R r K φ Q y
    Booked C N p 0 Y u un ∧ PaidAt (C).S N p J ((C).beta N p) expense (Y-report R Y u • (1:Cut C N p)) ∧
      ‖tested R A (N,p) r φ (WilsonThermometerUnitFilingRelative.table R (N,p) r φ Q)-report R Y u‖≤expense

def Primary {u J N p:ℕ} {r K:ℝ} {φ:Test 3} (S:Bank R N p u J r K φ) (A:Group C 6)
    (y:lifts (N:=N) (p:=p) R r φ):Prop:=
  ∀ (c:Grid R (N,p) r φ) (s:(J₃).Mode),
    WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level dims s.val) ((S.stock c).paths s.val) S.live.le
      (WilsonCapturedPrimaryFaceWallet.label R s.val (nominees R A (N,p))) (y c s)

def nominated {u J N p:ℕ} {r K:ℝ} {φ:Test 3} (S:Bank R N p u J r K φ) (A:Group C 6):
    lifts (N:=N) (p:=p) R r φ:=
  fun c s i=>WilsonNeutralOffsetCutoff.input R (p:=p) ((S.stock c).paths s.val i) S.live.le
    (WilsonCapturedPrimaryFaceWallet.label R s.val (nominees R A (N,p)) i)

theorem authentic {u J N p:ℕ} {r K:ℝ} {φ:Test 3} (S:Bank R N p u J r K φ) (A:Group C 6):
    Primary R S A (nominated R S A):=by
  intro c s
  exact WilsonCapturedPrimaryNamedReturn.sparse R (level dims s.val) ((S.stock c).paths s.val) S.live.le
    (WilsonCapturedPrimaryFaceWallet.label R s.val (nominees R A (N,p)))

include simple in
theorem original (book:OPE.Package C R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (slow:WilsonWindowReportingPace.Slow R.kit)
    (v J u:ℕ) (wide:4<v) (enlarged:(C).ref 0≤J) (ju:J≤u) (station:∀p,Opened C 0 u p)
    (tiling:Stock.Tabs.opens (C).path.levels 1 J u) (φ:Test 3) :
    ∃ K:ℝ,1≤K ∧ ∀ᶠ r in trail, ∀ N p,launch R simple v r<N→Nonempty (Bank R N p u J r K φ):=by
  obtain ⟨K,pos,issued⟩:=WilsonThermometerUnitFilingRelativeStation.original R simple book shop slow v J u
    wide enlarged ju station tiling φ
  refine ⟨K,pos,?_⟩
  filter_upwards [issued] with r resources N p hn
  obtain ⟨um,mk,offers⟩:=resources
  obtain ⟨S,price⟩:=offers N p hn
  exact ⟨⟨launch R simple v r,hn,um.trans ((capture R r).le_succ.trans (mk.le.trans hn.le)),
    S,price⟩⟩

end YM.Integration.WilsonThermometerUnitFilingReflectionBank
