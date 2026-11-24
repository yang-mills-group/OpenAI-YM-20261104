import YM.Integration.WilsonCapturedPrimaryActiveArms
import YM.Integration.WilsonThermometerCourseIntake

/-! The eight genuine station subwords on one paid original cell, with
the unit costs independent of the cutoff and of its displaced addresses. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryStationArms
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

def height (i : Fin 3) : ℕ := grade i

def nominees (A : Group C 6) (j : UVIndex) (i : Fin 3) : (C).label (height i) :=
  A.station.wheel.atCut j (index A (grade i)) (vector A Finset.univ i)

theorem finite_unit {f : Extraction.Order} {H : (Bel (C).book).Hierarchy} (A : Group C 6)
    (checked : A.station.checked f H A.horizon) (N p : ℕ) (late : A.station.k < N)
    (i : Fin 3) (start : (C).ref (height i) ≤ N) (z : Site ((C).side N p)) :
    (C).O N p (A.station.wheel.atCut (N,p) (index A (grade i))
      ((Bel (C).book).unit (grade i))) z = 1 := by
  let j := index A (grade i)
  have scalar : A.station.wheel.atCut (N,p) j ((Bel (C).book).unit j) = (C).book.scalar j := by
    change Next.Rank.East.ladd C _ _ _ _ _ _ (Further.CorrectedLift.ladder C j ((Bel (C).book).unit j))=_
    rw [Further.CorrectedLift.ladder_unit]
    exact Next.Rank.East.pure_start R.makes (checked.early j) (Nat.le_of_lt late)
      _ _ ((checked.rate _ _ late).1 j).1
  change (C).O N p (A.station.wheel.atCut (N,p) j ((Bel (C).book).unit j)) z = 1
  rw [scalar]; exact (C).constant R.makes j start z

theorem finite_face {f : Extraction.Order} {H : (Bel (C).book).Hierarchy} (A : Group C 6)
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel (C).book).unit t) = (Bel (C).book).unit t)
    (N p : ℕ) (late : A.station.k < N) (ref : ∀ i, (C).ref (height i) ≤ N)
    (s : Badge) (z : Fin 3 → Site ((C).side N p)) :
    placed R A (N,p) s z = fun U => ∏ i ∈ s, (C).O N p (nominees R A (N,p) i) (z i) U := by
  funext U
  have slot (i : Fin 3) : (C).O N p (A.station.wheel.atCut (N,p) (index A (grade i))
      (vector A s i)) (z i) U = if i ∈ s then (C).O N p (nominees R A (N,p) i) (z i) U else 1 := by
    by_cases hi : i ∈ s
    · have same : vector A s i = vector A Finset.univ i := by
        simp [vector,WilsonPositionThermometerGradedSource.source,hi]
      rw [if_pos hi,same]; rfl
    · rw [if_neg hi]
      have clear : vector A s i = (Bel (C).book).unit (grade i) :=
        (congrArg (A.change (grade i)) (WilsonPositionThermometerGradedSource.unit C s i hi)).trans (unit _)
      rw [clear]; exact congrFun (finite_unit R A checked N p late i (ref i) (z i)) U
  simp [WilsonThermometerCourseIntake.placed,slot]

include simple in
theorem original (book : OPE.Package C R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v h J u : ℕ) (wide : 4 < v) (enlarged : (C).ref h ≤ J)
    (station : ∀p, Opened C h u p) (tiling : Stock.Tabs.opens (C).path.levels 1 J u)
    (φ : Test 3) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ radius in trail,
    let m := capture R radius
    let k := launch R simple v radius
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ N p (kn : k < N) (z : Fin 3 → Site ((C).side N p)),
      WilsonCenteredCompactBooking.mass R φ radius (N,p) z ≠ 0 → ∀ ax : Fin 3,
      ∃ S : Shelf (N:=N) (p:=p) R k height (origin z ax),
      ∀ (f : Extraction.Order) (H : (Bel (C).book).Hierarchy) (A : Group C 6),
        A.station.checked f H A.horizon →
        (∀ t : Fin 7, A.change t ((Bel (C).book).unit t) = (Bel (C).book).unit t) →
        A.station.k < N → (∀ i, (C).ref (height i) ≤ N) →
        ∀ (s : Badge) (y : (i : Fin 3) → Palette C (level height s i)),
        WilsonCapturedPrimaryNamedReturn.primary R (p:=p) (level height s) (S.paths s) kn.le
          (label R s (nominees R A (N,p))) y →
        let un := um.trans (m.le_succ.trans (mk.le.trans kn.le))
        let Y := placed R A (N,p) s (origin z ax)
        Booked C N p h Y u un ∧ PaidAt (C).S N p J ((C).beta N p)
          (((∏ i ∈ s, (1+size (y i)))*2^(3-s.card)) * (K * radius^((h:ℝ)+1/32)))
          (WilsonCapturedPrimaryScaledCounter.difference R (station p) un Y) := by
  obtain ⟨K,one,sale⟩ := WilsonCapturedPrimaryActiveArms.original R simple book shop slow
    6 v h J u wide enlarged station tiling φ height (fun i => Nat.le_of_lt_succ (grade i).isLt)
  refine ⟨K,one,?_⟩
  filter_upwards [sale] with radius bought
  obtain ⟨um,mk,room⟩ := bought
  refine ⟨um,mk,?_⟩
  intro N p kn z active ax
  obtain ⟨S,all⟩ := room N p kn z active ax
  refine ⟨S,?_⟩
  intro f hierarchy A registered unit late starts s y hit
  have face := finite_face R A registered unit N p late starts s (origin z ax)
  change Booked C N p h (placed R A (N,p) s (origin z ax)) u _ ∧ PaidAt _ _ _ _ _ _ _
  rw [face]
  exact all s (nominees R A (N,p)) y hit

end YM.Integration.WilsonCapturedPrimaryStationArms
