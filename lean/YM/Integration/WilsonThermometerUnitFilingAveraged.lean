import YM.Integration.WilsonThermometerUnitFilingInvoice
import YM.Integration.WilsonThermometerUnitFilingRegistered

/-! The signed discounted capture measurement of a true shape in a common registered cell. The original unit filing can be compared with the independent group-field models under that same old conditional law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingAveraged
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom

variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b≤N) {u:ℕ} (floor:m≤u) (ub:u≤b)
   (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
open Source RG16 RG16.Literal WilsonThermometerUnitFilingCoarse Extraction Climb Bid
open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open WilsonThermometerCenteredAlgebra
open scoped Topology
open private smooth admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "V" => Ψ b
local notation "W" => R.family.path.rep N per b
local notation "X" => Config G (R.family.side b per)


open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16 RG16.Literal

open FVA1 OriginalForcedAddresses WilsonThermometerCourseHearing WilsonThermometerCourseIntake
open WilsonPositionThermometerCapStation WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open WilsonCenteredCloseOccupiedSale WilsonCenteredCloseCaptureWallet

open RG12 Primitives.GCC.Anchor
local notation "z!" => ((N,per):UVIndex)
local notation "J!" => Stock.census (Fin 3)

open MeasureTheory OPE.Therm
variable (A:Group R.family 6) (r:ℝ) (φ:Test 3) (table:Sites R ((N,per):UVIndex)→Poly (Stock.census (Fin 3))) (place:Sites R ((N,per):UVIndex)→Sites R ((N,per):UVIndex))
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z!)
local notation "Y!" => WilsonThermometerUnitFilingRegistered.submitted R A z! r φ table place
local notation "face!" y:max => WilsonThermometerUnitFilingCylinder.source R A z! (place y) (table y)
local notation "node!" y:max => credit R.family N per 0 (face! y) b top

include simple table place in
private theorem value (door:Trace.Physical.GermGraph.Opened R.family 0 u per)
    (book:Booked R.family N per 0 (Y!) u (ub.trans top)) :
    WilsonThermometerUnitFilingFeed.report R (Y!) u=∑y,w! y*WilsonThermometerUnitFilingCoarse.reading R (N:=N) (node! y) u ub:=by
  rw [WilsonThermometerUnitFilingCourse.filed R simple _ door (ub.trans top) book]
  unfold WilsonThermometerUnitFilingRegistered.submitted
  rw [IntrinsicProductLinearity.credit_sum R.family N per 0 u (ub.trans top) _ _
    (fun y=>admitted R A z! (place y) (table y)),Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro y _
  unfold WilsonThermometerUnitFilingCoarse.reading
  rw [WilsonThermometerUnitFilingCoarse.cutoff R top ub (face! y) (admitted R A z! (place y) (table y))]
  simp only [Pi.smul_apply,smul_eq_mul];ring

include simple table place way D Q ticket π Γ Ψ course floor gate in
theorem original (qualified:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z!)
    (door:Trace.Physical.GermGraph.Opened R.family 0 u per) (book:Booked R.family N per 0 (Y!) u (ub.trans top))
    (filed:Sites R z!→X→ℂ) (cap:ℝ) (positive:0≤cap)
    (paid:∀ t,w! t≠0 → ∃o:Positions (Fin 3) (R.family.side N per),o.origin=place t ∧
      ∃(y:Site (R.family.side b per)) (h:Coefficient F₀ (R.family.side b per)) (M:ℝ),0≤M ∧
      h.Format y R.family.params V ∧ h.remBound y V (LocalComparison.forcedDivisor R.family b) M ∧
      ‖h.x 0‖+5*M≤cap ∧
      ∀U,h.density y S₀ V U=(total (incoming R A simple top o U) (table t)).part full-((W).eval U:ℂ)*filed t U) :
    ‖WilsonThermometerUnitFilingFeed.report R (Y!) u-
      ∑t,w! t*WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>((W).eval U:ℂ)*filed t U) u ub‖≤(∫x:Points 3,‖φ x‖)*cap:=by
  let model (t:Sites R z!):=WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>((W).eval U:ℂ)*filed t U) u ub
  let delta (t:Sites R z!):=WilsonThermometerUnitFilingCoarse.reading R (N:=N) (node! t) u ub-model t
  rw [value R simple top ub A r φ table place door book,←Finset.sum_sub_distrib]
  have formed : (∑t,(w! t*WilsonThermometerUnitFilingCoarse.reading R (N:=N) (node! t) u ub-w! t*model t))=∑t,w! t*delta t:=
    Finset.sum_congr rfl fun t _=>(mul_sub ..).symm
  rw [formed]
  calc
    _ ≤ ∑t,‖w! t*delta t‖:=norm_sum_le _ _
    _ ≤ ∑t,‖w! t‖*cap:=by
      apply Finset.sum_le_sum;intro t _
      by_cases act:w! t=0
      · simp [act]
      · obtain ⟨o,loc,y,h,M,nn,fmt,rem,size,realData⟩:=paid t act
        have heard:=WilsonThermometerUnitFilingInvoice.sale R simple way D Q ticket π Γ Ψ course top
          floor ub gate A (table t) qualified o (filed t) y h fmt rem nn realData u le_rfl ub
        rw [loc] at heard
        exact (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (heard.trans size) (norm_nonneg _))
    _ ≤ _ :=by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation _ _
        (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z!)) positive

end YM.Integration.WilsonThermometerUnitFilingAveraged
