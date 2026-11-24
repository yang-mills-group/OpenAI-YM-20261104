import YM.Integration.WilsonThermometerUnitFilingRetention
import YM.Integration.WilsonThermometerUnitFilingCourse
import YM.Integration.WilsonThermometerBornCredit
import YM.Push.RELAY_DIFFERENCE.Rates

/-! The original native cutoff filing of the complete signed three-field
cylinder and every older scalar read of that same cylinder. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingBirth

open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells Extraction Spec Table Push.RelayDifference
open OPE Marker Next.Extract PhysicalNext.Repeat.Legato XSpace MergeProof RG12 RG16 RG16.Literal
open Extra.Histories Relay Next.Rank Primitives.GCC.Anchor Push.GridApprox
open Climb Trace.Pilot Next.UVStress RG17 PhysMS MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace.Normalize XSpace.Rose Work.G08 Trace.Physical
open Trace.Physical.GermGraph Bid WilsonPositionThermometerCapStation
open WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open WilsonThermometerCenteredAlgebra WilsonThermometerUnitFilingFeed
open scoped BigOperators Topology Classical
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "J!" => Stock.census (Fin 3)

include simple in
/-- At every admitted regulator the authenticated compact source on its
actual child cells has one original terminal ticket and all native scalar
reports. Its finite price can depend on the cutoff and fit. -/
theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (units : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ (u : ℕ) (_ : u ≤ z.1) (_ : R.family.ref 0 ≤ u)
      (r : ℝ) (φ : Test 3) (Q : Sites R z → Poly J!),
      let Y := cylinder R A z r φ Q
      ∃ (B : R.family.label 0) (E : ℝ), Next.UVStress.quota R.family 0 z.1 z.1 z.2 B ≤ 2*E ∧
        ∀ j, u ≤ j → ∀ live : j ≤ z.1, Opened R.family 0 j z.2 →
          Booked R.family z.1 z.2 0 Y j live ∧
          report R Y j =
            ((R.family.path.rep z.1 z.2 j).eval (1:Config G (R.family.side j z.2)):ℂ)⁻¹ *
            credit R.family z.1 z.2 0 Y j live 1 ∧
          ‖report R Y j-B 0‖ ≤ E/gainChart R.family.path z.1 j := by
  have upper := (cutoff_grows f).eventually (WilsonThermometerBornCredit.original R simple)
  have refs := eventually_all.mpr (fun j : Fin 3=>
    (cutoff_grows f).eventually_ge_atTop
      (R.family.ref (WilsonPositionThermometerGradedSource.grade j)))
  filter_upwards [upper,refs,WilsonThermometerUnitFilingRetention.original R A simple checked units]
    with z install certificates keep
  intro u live start r φ Q Y
  let o (y : Sites R z) : Positions (Fin 3) (R.family.side z.1 z.2) :=
    ⟨y,(fun j=>{y j}),(fun _=>Finset.mem_singleton_self _)⟩
  choose rent q _hn fmt paid bound _density valued using fun y : Sites R z=>
    install z.2 A (o y) 0 (Q y)
  let Ψ := R.family.path.rep z.1 z.2 z.1
  have held (y : Sites R z) (U : Config G (R.family.side z.1 z.2)) :
      (q y).density 0 (R.family.localSection 0) Ψ U =
        ∑ s : (J!).Mode,wallet (Q y) s * (incoming R A simple (le_refl z.1) (o y) U).part s := by
    rw [←valued y,WilsonThermometerLiteralCredit.returned R A simple (o y) (Q y) certificates le_rfl]
    exact affine _ _
  obtain ⟨_,B,quota,read⟩ := keep z.1 u le_rfl live start r φ Q o (fun _=>rfl) rent 1 zero_lt_one
    (fun y _=>⟨q y,fmt y,paid y,bound y,held y⟩)
  refine ⟨B,_,quota,?_⟩
  intro j uj ij op
  obtain ⟨book,price⟩:=read j uj ij op
  exact ⟨book,WilsonThermometerUnitFilingCourse.filed R simple Y op ij book,price⟩

end YM.Integration.WilsonThermometerUnitFilingBirth
end
