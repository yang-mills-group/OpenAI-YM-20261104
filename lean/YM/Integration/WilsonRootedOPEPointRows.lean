import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.WilsonRootedOPEPointFloor

/-! The exact weight-zero point orbit and clipped input width give a finite
charge per actual tensor/path row before specifying a point or period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointRows
open Function Finset Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges
open FullQLocal FullQLocal.RenderedStep Tensor RG05Readout.Native Push.PriceCompiler PhysicalNext.JointLoad ComparisonDensity.Address
open scoped BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G} (R:Run G)
variable (u:V→MS.Rake.Label B) (J:Request V) {p L:ℕ} (o:V→Site (R.family.side L p))
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J p L o

def reader : ℝ := ‖ActualOriginalQPointDatum.phase‖*NativeCalibrationMoodReadout.coordinateCost 0

omit [DecidableEq V] [Fintype V] in
theorem point (i:V) : readerPrice D₀ i = reader := by
  change readerPrice (ActualOriginalQPointDatum.datum R p L o (fun j=>(J.tests j).D) (fun _=>0)) i = _
  unfold readerPrice
  rw [ActualOriginalQPointDatum.constant_eq,ActualOriginalQPointDatum.depth_zero,pow_zero,one_mul]
  change ‖ActualOriginalQPointDatum.phase‖*(NativeCalibrationMoodReadout.coordinateCost 0*((1+‖_‖)^0)) = reader
  rw [pow_zero,mul_one]
  rfl

def tariff (z:Row (R:=R) u) : ℝ := WilsonRootedOPEGlyph.mass R u z * reader * Real.exp (rowFall u z)

omit [DecidableEq V] [Fintype V] in
theorem nonneg (z:Row (R:=R) u) : 0 ≤ tariff R u z := by
  have price : 0 ≤ reader := by
    unfold reader NativeCalibrationMoodReadout.coordinateCost
    exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (write_cost _).choose_spec.1.le (by positivity)) (by positivity))
  exact mul_nonneg (mul_nonneg (WilsonRootedOPEGlyph.mass_nonneg R u z) price) (Real.exp_pos _).le

theorem bounded {width:ℝ} (hw:width≤1) (z:Row (R:=R) u) :
    rowPrice D₀ u (fun _=>1) width z ≤ tariff R u z := by
  have reorder : rowMass D₀ u z=WilsonRootedOPEGlyph.mass R u z*readerPrice D₀ z.1.1 := by
    unfold rowMass WilsonRootedOPEGlyph.mass;ring
  have base : 0 ≤ WilsonRootedOPEGlyph.mass R u z*reader := by
    rw [←point R J o z.1.1]
    exact mul_nonneg (WilsonRootedOPEGlyph.mass_nonneg R u z) (zero_le_one.trans (WilsonRootedOPEPointFloor.unit R o (fun j=>(J.tests j).D) (fun _=>0) z.1.1))
  rw [rowPrice,reorder,point R J o,show Poly.toll (fun _:V=>1) ((Stock.census V).fire z.1.1)=1 by simp [Poly.toll],one_mul]
  apply mul_le_mul_of_nonneg_left _ base
  apply Real.exp_le_exp.mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (rowFall u z))

end YM.Integration.WilsonRootedOPEPointRows
