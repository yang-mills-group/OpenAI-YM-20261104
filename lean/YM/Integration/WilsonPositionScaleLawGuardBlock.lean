import YM.Integration.WilsonPositionScaleLawGuardNear
import YM.Integration.WilsonPositionScaleLawGuardOrbit

/-! The actual lower homogeneous grades receive only the all-order two-home remainder from other grades. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBlock
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGrade (grade)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGuardPhysical (expected)
open scoped Topology Classical Asymptotics

theorem charge {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](P U N:X→L[ℂ]X)(η:ℂ)(x y:X)
    (change:P (U y)=η • P x)(graded:∀v,P (N v)=N (P v))(near:‖N-1‖≤1/4):
    3*‖P y‖≤4*‖η‖*‖P x‖+4*‖P‖*‖U-N‖*‖y‖:=by
  have identity:P y=P (U y)+P ((N-U) y)+(1-N) (P y):=by
    change P y=P (U y)+P (N y-U y)+(P y-N (P y))
    rw [P.map_sub,graded];abel
  have defect:‖P ((N-U) y)‖≤‖P‖*(‖U-N‖*‖y‖):=by
    rw [norm_sub_rev U N]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((N-U).le_opNorm _) (norm_nonneg _))
  have small:‖(1-N) (P y)‖≤(1/4)*‖P y‖:=by
    have hh:‖1-N‖≤1/4:=(norm_sub_rev (1:X→L[ℂ]X) N).trans_le near
    exact ((1-N).le_opNorm _).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
  have law:‖P y‖≤‖η‖*‖P x‖+‖P‖*(‖U-N‖*‖y‖)+(1/4)*‖P y‖:=calc
    _=‖P (U y)+P ((N-U) y)+(1-N) (P y)‖:=congrArg norm identity
    _≤‖P (U y)+P ((N-U) y)‖+‖(1-N) (P y)‖:=norm_add_le _ _
    _≤(‖P (U y)‖+‖P ((N-U) y)‖)+(1/4)*‖P y‖:=add_le_add (norm_add_le _ _) small
    _≤_:=by rw [change,norm_smul];exact add_le_add (add_le_add le_rfl defect) le_rfl
  linarith

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
include H in
theorem original (funded:Coupling G (kinetic Z F J)){d:ℕ}(q:ℕ)(i:Fin (d+1))(lower:i.val<d):
    ∀ᶠr in trail,∀t:Ratio,∀O:S.Field d,
      let y:=physical F J Z d (t.val*r) O
      let x:=physical F J Z d r O
      let U:=dressed Z F J d r t
      let N:=expected F J Z M ν d q r t
      3*‖grade R.family i y‖≤4*t.val*‖grade R.family i x‖+4*‖grade R.family i‖*‖U-N‖*‖y‖:=by
  filter_upwards [WilsonPositionScaleLawGuardNear.measured Z M H ν F J funded d q] with r ready t O
  intro y x U N
  let P:=grade R.family i
  have ht:=WilsonPositionScaleLawNative.positive t
  have shrink:‖(t.val:ℂ)^(d-i.val)‖≤t.val:=by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (show d-i.val≠0 by omega)
    rw [hk,pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le t.property.2 (n:=k)) ht.le
  have bill:=charge P U N ((t.val:ℂ)^(d-i.val)) x y (WilsonPositionScaleLawGuardOrbit.step F J Z r t i O)
    (WilsonPositionScaleLawGuardDiagonal.original R.family Z M H ν _ i q _) (ready t)
  exact bill.trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left shrink (by norm_num : (0:ℝ)≤4)) (norm_nonneg _)) le_rfl)

end YM.Integration.WilsonPositionScaleLawGuardBlock
