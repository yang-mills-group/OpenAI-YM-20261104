import YM.Integration.WilsonPositionProgramFilmGroundReturn
import YM.Integration.WilsonThermometerPositionFilmAngularGround
import YM.Integration.WilsonThermometerOriginalFilmRows

/-! The exact original conditional Gaussian on one positioned field, including an already grouped word. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmSingleton
open Function MeasureTheory Finset Lattice RG Wilson Precision Tree Exterior Marker Multi
open Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Symmetry
open Comparison.RG02.Assembly Primitives.GCC.Anchor WilsonThermometerPositionFilmCubicGeometry
open Comparison.RG02.Cumulants PertExtension.Series YM.Next.SectorChange WilsonThermometerPositionFilmChartContact
open WilsonThermometerPositionFilmCloudReading WilsonThermometerOriginalCoveredRows
open scoped BigOperators Classical
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{R:Census V}

theorem seed (W:Poly R)(mass:W.part R.quiet=0)(u:V):
    W.pass.part (R.fire u)=W.part (R.fire u):=by
  have nz:R.fire u≠R.quiet:=by intro eq;have e:=congrArg Subtype.val eq;simp [Census.fire,Census.quiet] at e
  have card:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨u⟩
  unfold Poly.pass
  rw [Poly.part_sum, sum_eq_single 1]
  · simp
  · intro j _ hj
    by_cases hz:j=0
    · subst j;simp [nz]
    · rw [Poly.part_smul, Poly.high W mass j (R.fire u) (by simp [Census.fire];omega),mul_zero]
  · simp [card]
theorem logSeed (W:Poly R)(mass:W.part R.quiet=1)(u:V):
    (connected W).part (R.fire u)=W.part (R.fire u):=by
  rw [←seed (connected W) (connected_quiet mass) u,pass_connected mass]

variable {c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  (W:Bulk.Colors R G f)(u:V)(A:fieldDir G c 1)
local notation "Y" => Bulk.Fk K F tag W A 1
local notation "μ" => Gaussian.cloud (K.covariance F tag)

theorem original (hw:∀t,GradeAt (W.power t) (Bulk.projected (W.mark t))):
    (observe R 0 (logMarked (Bulk.Fk K F tag W A 0)) 0).part (R.fire u)=
    ∫z,(QuadraticLocal.Earn.Air.discharge W 0 (direction F (Bulk.translated K F A z).2)).part (R.fire u) ∂μ:=by
  have raw:=joint K F tag W A 1 (by decide)
  have head:First.buc Y=base K F tag W A:=raw.1
  have unit:(base K F tag W A).part R.quiet=1:=by rw [←head,First.buc_vac,Bulk.fk_unit]
  have earned := (signed K F tag W A 1 (by decide)).1
  rw [←WilsonOriginalReceivedGradeRestriction.original K F tag W A (show 0≤1 by decide) 0 (Nat.zero_le _)]
  change (First.buc (logMarked Y)).part (R.fire u)=_
  rw [earned,logSeed _ unit,←head]
  rw [show First.buc Y=observe R 1 Y 0 from rfl,observed K F tag W (R.fire u) A 1 0 (Nat.zero_le _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [WilsonThermometerPositionFilmAngularGround.received F W hw K tag (R.fire u) A z]
  apply seed
  exact Multi.part_lit_quiet ..

end YM.Integration.WilsonPositionProgramFilmSingleton
end
