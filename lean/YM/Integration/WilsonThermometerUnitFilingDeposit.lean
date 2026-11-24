import YM.Integration.WilsonThermometerUnitFilingCylinder
import YM.Integration.WilsonThermometerUnitFilingReturn
import YM.Integration.IntrinsicProductLinearity

/-! The full compact signed source on the original deposited Wilson law,
before hearing either its previous conditional means or its fixed scalar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingDeposit
open Filter Function Set Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox RG16.Literal
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "C" => R.family
local notation "j!" => Stock.census (Fin 3)

private theorem smooth (z : UVIndex) (y : Sites R z) (s : (j!).Mode) :
    Continuous (placed R A z s.val y) := by
  apply continuous_finsetProd
  intro i _
  exact R.family.continuousO z.1 z.2 _ _ _

private theorem admitted (z : UVIndex) (y : Sites R z) (Q : Poly j!) :
    Continuous (WilsonThermometerUnitFilingCylinder.source R A z y Q) := by
  unfold WilsonThermometerUnitFilingCylinder.source
  rw [show (∑ s : (j!).Mode,wallet Q s • placed R A z s.val y)=_ from funext (fun U=>Finset.sum_apply U _ _)]
  exact continuous_finsetSum _ fun s _=>(smooth R A z y s).const_smul _

include simple in
/-- The same signed cylinder at every earlier date, using each three-site
gallery's actual roots and unmodified quiet and compulsory entries. -/
theorem field {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly j!)
      (o : Sites R z → Positions (Fin 3) (R.family.side z.1 z.2)) (_ : ∀y,(o y).origin=y)
      (U : Config G (R.family.side k z.2)),
      credit C z.1 z.2 0 (cylinder R A z r φ Q) k upper U=
        ∑y,WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z) y *
          ∑s : (j!).Mode,wallet (Q y) s * (incoming R A simple upper (o y) U).part s := by
  filter_upwards [WilsonThermometerUnitFilingReturn.density R A simple checked unit] with z receipts k upper r φ Q o located U
  unfold WilsonThermometerUnitFilingCylinder.cylinder
  dsimp only
  rw [IntrinsicProductLinearity.credit_sum C z.1 z.2 0 k upper _ _ (fun y=>admitted R A z y (Q y))]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [WilsonThermometerUnitFilingCylinder.source,IntrinsicProductLinearity.credit_sum C z.1 z.2 0 k upper _ _ (smooth R A z y)]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply congrArg (_ * ·)
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg (_ * ·)
  simpa only [located] using (congrFun (receipts k upper (o y) s) U).symm

include simple in
/-- Integrate the fully signed deposited table under the real old Haar prior
and divide by its positive original vacuum once, at every earlier scale. -/
theorem normalized {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1) (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly j!)
      (o : Sites R z→Positions (Fin 3) (R.family.side z.1 z.2)) (_ : ∀y,(o y).origin=y),
      (∫ U, ∑y,WilsonSeparatedOriginalThermometerCells.weight φ (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z) y *
          ∑s : (j!).Mode,wallet (Q y) s * (incoming R A simple upper (o y) U).part s
            ∂prior G (R.family.side k z.2)) /
        (∫ U,((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2))=
          WilsonThermometerUnitFilingCylinder.tested R A z r φ Q := by
  filter_upwards [field R A simple checked unit] with z each k upper r φ Q o placed_at
  simp_rw [←each k upper r φ Q o placed_at]
  rw [credit_moment C z.1 z.2 0 R.makes _ (continuous_cylinder R A z r φ Q) upper,pow_zero,one_mul]
  have mass : (∫ U, ((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2)) =
      (partition G (R.family.side z.1 z.2) (R.family.beta z.1 z.2) : ℂ) :=
    (integral_ofReal ..).trans (congrArg Complex.ofReal (History.partition_eq R.family.path R.makes.wilson z.1 z.2 k upper))
  have pos : (∫ U, ((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2)) ≠ 0 :=
    mass ▸ Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  rw [mul_div_cancel_left₀ _ pos]
  exact WilsonThermometerUnitFilingCylinder.literal R A z r φ Q

end YM.Integration.WilsonThermometerUnitFilingDeposit
