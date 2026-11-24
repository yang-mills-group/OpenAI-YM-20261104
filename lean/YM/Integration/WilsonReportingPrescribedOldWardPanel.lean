import YM.Integration.WilsonReportingPrescribedOldWardWallet
import YM.Integration.WilsonReportingPrescribedOldSignedPanel

/-! The full signed action and spectator are compared on their original
separated two-point test, using their actual deposited and prescribed vectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldWardPanel
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 SectorNext.Vacuum Extraction Table Spec Climb
open MS MS.Local.Physical MS.Theater Maxwell Maxwell.Free StressFlux Trace Trace.Pilot PhysMS
open Extraction.Order MS.Menus Next.UVStress OPE OPE.Therm FVA2 FVA2.Register WilsonReportingPrescribedOldCoordinates
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldSignedPanel
open WilsonReportingPrescribedOldWardWallet WilsonInvariantActionSpectatorPrices WilsonPositionHomogeneousFrame
open private read_sub from YM.Integration.WilsonReportingPrescribedOldGram
open private issued_cont polarized from YM.Integration.WilsonReportingPrescribedOldSignedPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {B:Deck G} (Q:MS.Land.Prescription B) {N per:ℕ}
local notation "Ω" => Config G (R.family.side N per)
local notation "site" => Site (R.family.side N per)

def column (z:Stock B) (clock:ℝ) (k:ℕ) : Panel R 4 :=
  fun a=>∑i,z.2 i • prescribed R Q (WilsonReportingPrescribedOldAction.label B i) clock k a

theorem readout (z:Stock B) (clock:ℝ) (k:ℕ) (o:site) (U:Ω) :
    operand R Q z clock k (R.family.side N per) o U=
      (if k=0 then z.1 else 0)+read R o U (column R Q z clock k) := by
  unfold operand
  congr 1
  unfold WilsonReportingPrescribedOldCoordinates.read column
  simp_rw [map_sum,map_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [WilsonReportingPrescribedOldCoordinates.independent,←Finset.mul_sum]
  rfl

def gap (v:R.family.label 4) (z:Stock B) (clock:ℝ) (k:ℕ) (o:site) (U:Ω) : ℂ :=
  read R o U (entering R N per (by decide : 4≤4) v-column R Q z clock k)-
    (if k=0 then z.1 else 0)

theorem difference (v:R.family.label 4) (z:Stock B) (clock:ℝ) (k:ℕ) (o:site) (U:Ω) :
    gap R Q v z clock k o U=R.family.O N per v o U-operand R Q z clock k (R.family.side N per) o U := by
  unfold gap
  rw [read_sub,asReported,readout]
  ring

private theorem continuous_operand (z:Stock B) (clock:ℝ) (k:ℕ) (o:site) :
    Continuous (operand R Q z clock k (R.family.side N per) o) := by
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (issued_cont R Q (WilsonReportingPrescribedOldAction.label B i) clock k o)

variable {R}

theorem original {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (J:ℝ→tower S) (Z:WilsonPrescription G) (L:Layout F) (simple:G.Simple)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (v:RG17.Free R.family 4)
    (χ:ℂ→L[ℝ]ℝ) (φ:Test 2) {r:ℝ} (hr:0<r) (μ:ℝ) (k l:ℕ) (N per:ℕ) :
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let x:=atRef L 4 r (N,per) (a r)
    let y:=atRef L 4 r (N,per) (b r)
    let clock:=μ-R.family.S.scale N
    let z:=spectator F J Z simple B r v
    let n:=R.family.side N per
    let A:=operand R Q (WilsonReportingPrescribedOldWardWallet.action B) clock k n
    let D:=operand R Q z clock l n
    let ψ:=dilate hr φ
    WilsonMatrixOriginalFiledPanel.Value F L a b χ φ hr (N,per)-
        separated R (N:=N) (per:=per) χ ψ A D=
      separated R (N:=N) (per:=per) χ ψ
        (gap R Q x (WilsonReportingPrescribedOldWardWallet.action B) clock k) (R.family.O N per y)+
      separated R (N:=N) (per:=per) χ ψ A (gap R Q y z clock l) := by
  dsimp only
  unfold WilsonMatrixOriginalFiledPanel.Value WilsonMatrixOriginalSignedReading.signed WilsonReportingPrescribedOldSignedPanel.separated
  rw [←mul_sub,←mul_add]
  apply congrArg
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub,←mul_add]
  apply congrArg (fun t=>(dilate hr φ (cells R.family N per i)).re*t)
  simp_rw [difference]
  simp only [Complex.sub_re,map_sub]
  apply polarized
  · exact Complex.continuous_re.comp (R.family.continuousO ..)
  · exact χ.continuous.comp (R.family.continuousO ..)
  · exact Complex.continuous_re.comp (continuous_operand R Q ..)
  · exact χ.continuous.comp (continuous_operand R Q ..)

end YM.Integration.WilsonReportingPrescribedOldWardPanel
