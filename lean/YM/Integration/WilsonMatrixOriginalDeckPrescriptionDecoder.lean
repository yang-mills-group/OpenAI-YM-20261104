import YM.Integration.WilsonMatrixOriginalDeckRawDecoder
import YM.Integration.WilsonMatrixOriginalDeckPrescriptionGram

/-! Execute the independently prescribed two-clock candidate on the original physical Gram before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionDecoder
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 MS MS.Land MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm FVA2.ColorCode
open Trace.Pilot WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckError WilsonMatrixOriginalDeckFiledDebit
open WilsonMatrixOriginalDeckRawAssay
open scoped Classical Topology BigOperators Matrix

variable {G:Gauge} (R:Run G) {D:Deck G} (Q:MS.Land.Prescription D){f:Extraction.Order}{S:Table R.family.book}
variable (F:Spec.Final R.family f S)(L:Layout F)(J:ℝ→PhysMS.tower S)(h:ℕ){O:Booked D}
local notation "I"=>Glyph D h

local notation "roster" => WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=D) h
local notation "transfer" => WilsonMatrixOriginalDeckPrescriptionSeries.trial Q h

theorem original (lead:PhysMS.Leading F J)(M:MS_Data G O)(g:Test 2)(pivot:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)):
    ∃K:ℝ,0<K ∧ ∀ᶠr:ℝ in trail, ∀(hr:0<r)(_:R.family.ref h≤L.level r)(w:I→R.family.label h),
      (∀i,master L h r (w i)=J r h (WilsonMatrixOriginalDeckColumns.basis R.family D h i)) →
      ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens → ∀ᶠz in u, ∀(s:ℝ)(v:I→R.family.label h)(μ ν:ℝ),
      let T:=dilate hr g
      let a:=roster μ 0
      let b:=roster ν 0
      let V:=transfer μ ν 0
      let E:=signed R F L Q h T z r s w v a b
      let H:=signed R F L Q h T z r r w w a a
      amount ((field R D F L h g hr r w w z)⁻¹*field R D F L h g hr s w v z-V) ≤
        K*amount (E-H*V):=by
  obtain ⟨K,hK,paid⟩:=WilsonMatrixOriginalDeckRawDecoder.original R Q F L J h lead M g pivot
  refine ⟨K,hK,?_⟩;filter_upwards [paid] with r settled
  intro hr age w deliver u _ cut
  filter_upwards [settled hr age w deliver u cut] with z live
  intro s v μ ν
  have pay:=live s v (roster μ 0) (roster ν 0) (transfer μ ν 0)
  have balanced:=WilsonMatrixOriginalDeckPrescriptionGram.born R Q h (dilate hr g) z (roster μ 0) μ ν
  have zero:amount (matrix R Q h (dilate hr g) z (roster μ 0) (roster ν 0)-
      matrix R Q h (dilate hr g) z (roster μ 0) (roster μ 0)*transfer μ ν 0)=0:=by
    rw [balanced,sub_self];simp [WilsonMatrixOriginalDeckRelative.amount]
  simpa only [zero,zero_add] using pay

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionDecoder
