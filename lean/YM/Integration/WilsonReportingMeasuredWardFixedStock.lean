import YM.Integration.WilsonReportingMeasuredWardIntake
import YM.Integration.WilsonReportingMeasuredWardFeePrice
import YM.Integration.WilsonMatrixOriginalGermRedemption

/-! The true old normalized curvature stock and the independently filed order-zero source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardFixedStock
open Function Finset Lattice Wilson RG Source Labels MS.Local.Physical MS.Theater MS.Land
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph Next.Rank.Price
open WilsonReportingPrescribedOldFreeArms WilsonReportingMeasuredWardFees
open WilsonReportingMeasuredWardSource WilsonReportingMeasuredWardSourceGerm
open WilsonReportingMeasuredWardIntake WilsonMatrixTicketLanesNativePrices
open scoped BigOperators Classical

variable {G:Gauge} {B:Deck G} {R:Run G} {T:Campaign R}
    (W:Campaign.Pillars R T) (Q:Prescription B) {m N per:ℕ}
local notation "F" => R.family.labels.level 4
local notation "I" => B.BIndex (4:ℤ) 2

def issued (opened:Opened R.family 4 m per) (life:m ≤ N) (z:Stock B):R.family.label 4:=
  ∑i:I,z.2 i • WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=per)
    (WilsonMatrixOriginalGermRedemption.calibrated R opened life) (WilsonMatrixOriginalCurvatureStock.curvature B i)

theorem physical (age:R.family.ref 4 ≤ m) (life:m ≤ N) (z:Stock B) (clock:ℝ) (k:ℕ):
    let q:=charged W Q (per:=per) life 0 z clock k
    (F).scaled (shrink R.family m N per)
      ((↑(R.family.S.a m^4):ℂ)⁻¹ • Trace.Physical.GermGraph.page (C:=R.family) 4 per m q)=
      scalar R Q z clock k • (F).e0+
        ((Pert.Asymptotics.regulatorRun R.family N per m^2:ℝ):ℂ) • coordinates R (projected Q clock k z) := by
  intro q
  have h:= (entered W Q (per:=per) age life z clock k).2
  rw [h,Complex.ofReal_pow,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')),one_smul]
  rw [←WilsonReportingMeasuredWardSourceGerm.measured R Q m per age]
  exact WilsonReportingMeasuredWardSourceGerm.calibrated R Q m N per age z clock k

theorem matrix_zero (z:Stock B) (clock:ℝ) (j:I):(projected Q clock 0 z).2 j=z.2 j:=by
  unfold projected
  simp [WilsonReportingMeasuredWardFeePrice.tree,mul_ite]

/-- The scalar here is fixed before the old regulator and its period. -/
theorem restored (simple:G.Simple) (z:Stock B) :
    ∃a:ℂ,∀{m N per:ℕ}(opened:Opened R.family 4 m per)(life:m ≤ N),
    (F).scaled (shrink R.family m N per) (WilsonMatrixOriginalGermMarket.normalized R m N per (issued opened life z))=
      coordinates R z+a • (F).e0 := by
  choose c bill using WilsonMatrixOriginalCurvatureField.corrected (warehouse R) B simple
  refine ⟨∑i:I,z.2 i*c i,?_⟩
  intro m N per opened life
  let L:=WilsonMatrixOriginalGermRedemption.calibrated R opened life
  let A:=((R.family.factory 4 N per).terminal.symm.trans L).toLinearMap
  have read (v:R.family.label 4): A v=(F).scaled (shrink R.family m N per) (WilsonMatrixOriginalGermMarket.normalized R m N per v):=rfl
  let u (i:I):=WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=per) L (WilsonMatrixOriginalCurvatureStock.curvature B i)
  have named (i:I):A (u i)=(show R.family.label 4 from (warehouse R).fits B 4 2 i)+c i • (F).e0:=by
    rw [read]
    exact (WilsonMatrixOriginalGermRedemption.named R B opened life (WilsonMatrixOriginalCurvatureStock.curvature B i)).trans (bill i)
  rw [←read,issued,map_sum]
  change (∑i:I,A (z.2 i • u i))=_ 
  simp only [map_smul,named,smul_add,smul_smul,Finset.sum_add_distrib,Finset.sum_smul]
  rfl

/-- The measured old germ of each fixed stock has the full physical running normalization. -/
theorem original (simple:G.Simple) (z:Stock B) :
    ∃a:ℂ,∀{m N per:ℕ}(opened:Opened R.family 4 m per)(life:m ≤ N)(clock:ℝ),
    let q:=charged W Q (per:=per) life 0 z clock 0
    let A:=(F).scaled (shrink R.family m N per)
    let g:=Pert.Asymptotics.regulatorRun R.family N per m
    A ((↑(R.family.S.a m^4):ℂ)⁻¹ • Trace.Physical.GermGraph.page (C:=R.family) 4 per m q)=
      scalar R Q z clock 0 • (F).e0+
        ((g^2:ℝ):ℂ) • (A (WilsonMatrixOriginalGermMarket.normalized R m N per (issued opened life z))-a • (F).e0) := by
  obtain ⟨a,old⟩:=restored (R:=R) simple z
  refine ⟨a,?_⟩
  intro m N per opened life clock q A g
  rw [old opened life,add_sub_cancel_right]
  have xy:coordinates R (projected Q clock 0 z)=coordinates R z:=by
    unfold coordinates
    exact sum_congr rfl (fun i _=>by rw [matrix_zero Q z clock i])
  exact (physical W Q opened.post life z clock 0).trans (by rw [xy])

end YM.Integration.WilsonReportingMeasuredWardFixedStock
