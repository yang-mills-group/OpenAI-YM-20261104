import YM.Integration.WilsonGeometricSignedCapture
import YM.Integration.WilsonThermometerRegisteredAncestralProperTest
import YM.Integration.WilsonThermometerUnitFilingReflectionBank
import YM.Integration.WilsonThermometerUnitFilingWhole

/-! Signed physical readings of the registered three cutoff fields and their exact deposited proper faces. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedFaceCylinder

open Finset Function Filter Lattice Wilson RG Labels Source Marker Cells MeasureTheory RG16 RG16.Literal
open Extraction Climb Next.UVStress Trace.Physical.GermGraph PhysicalNext.Repeat.Legato XSpace XSpace.Rose
open Table Spec Trace Trace.Pilot Push GridApprox FVA1 RG12 PhysMS OPE.Cards Primitives.GCC.Anchor
open Next.Foundations WilsonPositionThermometerCapStation
open WilsonThermometerUnitFilingFeed WilsonThermometerCourseIntake WilsonThermometerCenteredAlgebra
open WilsonGeometricSignedCapture WilsonThermometerFiniteConnectedCells
open private smooth_face smooth_sum linear_mean from YM.Integration.WilsonThermometerUnitFilingCylinder
open scoped Classical BigOperators
local notation "J₃" => Stock.census (Fin 3)

def restricted (Q : Poly J₃) (selected s : (J₃).Mode) : ℂ :=
  ∑ b:(J₃).Mode, if Poly.merges s b selected then (Primitives.GCC.Anchor.inverseMass Q).part b else 0

theorem restricted_value (F Q : Poly J₃) (s : (J₃).Mode) :
    (total F Q).part s = take (restricted Q s) F := by
  simp only [total,Poly.part_mul,take,restricted,Finset.sum_mul]
  apply sum_congr rfl;intro a _
  apply sum_congr rfl;intro b _
  by_cases ok : Poly.merges a b s <;> simp [ok,mul_comm]

theorem missing (Q:Poly J₃) (selected s:(J₃).Mode) (apart : ¬s.val⊆selected.val) :
    restricted Q selected s=0 := by
  apply sum_eq_zero;intro b _
  apply if_neg;intro both;apply apart
  rw [←both.2];exact subset_union_left

variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple)
  {N per:ℕ} (o:FVA1.Positions (Fin 3) (R.family.side N per))
local notation "z" => ((N,per):UVIndex)
local notation "Z" => (Cut R.family N per)
local notation "F" s:max => placed R A z (s).val o.origin

def source (c:(J₃).Mode→ℂ):Z := ∑s,c s • F s

theorem smooth (c:(J₃).Mode→ℂ) : Continuous (source R A o c) :=
  smooth_sum R z c _ (smooth_face R A z o.origin)

theorem observation (c:(J₃).Mode→ℂ) :
    R.family.omega N per (source R A o c)=take c (measured R A z o.origin) :=
  linear_mean R z c _ (smooth_face R A z o.origin)

theorem condition (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple z)
    {i:ℕ} (live:i≤N) (c:(J₃).Mode→ℂ) :
    credit R.family N per 0 (source R A o c) i live =
      fun U=>take c (incoming R A simple live o U) := by
  rw [source,IntrinsicProductLinearity.credit_sum R.family N per 0 i live c _ (smooth_face R A z o.origin)]
  funext U; rw [Finset.sum_apply];unfold take
  apply sum_congr rfl;intro s _
  rw [←qual.1 i live o s];rfl

include simple in
theorem heard (c:(J₃).Mode→ℂ) {u i j:ℕ} (ju:j≤u) (ui : u ≤ i) (live:i≤N) (door:Opened R.family 0 u per)
    (price:(J₃).Mode→ℝ) (arms:∀s,c s≠0→
      Booked R.family N per 0 (F s) u (ui.trans live) ∧
      PaidAt R.family.S N per j (R.family.beta N per) (price s)
        ((F s)-report R (F s) u • (1:Z))) :
    Booked R.family N per 0 (source R A o c) u (ui.trans live) ∧
    ‖take c (measured R A z o.origin)-report R (source R A o c) u‖ ≤ ∑s,‖c s‖*price s := by
  letI : Nonempty (J₃).Mode := ⟨(J₃).quiet⟩
  obtain ⟨book,pay⟩:=WilsonThermometerUnitFilingPaidBlend.original R simple c _ ju ui live door
    (smooth_face R A z o.origin) price arms
  refine ⟨book,?_⟩
  let Y:=source R A o c
  let T:=center R.family.S per (ju.trans (ui.trans live)) 0
  have bound:=(OPE.Strobe.atone T (R.family.beta N per) (seamless R.makes N per) pay.ticket).trans pay.mark
  change ‖R.family.omega N per (Y-report R Y u • (1:Z))‖ ≤ _ at bound
  have mu:R.family.omega N per (Y-report R Y u • (1:Z))=R.family.omega N per Y-report R Y u:=by
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact (smooth R A o c).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  rwa [mu,observation] at bound

end YM.Integration.WilsonThermometerNominatedFaceCylinder
