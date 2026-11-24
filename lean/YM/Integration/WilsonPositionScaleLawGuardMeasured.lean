import YM.Integration.WilsonPositionScaleLawGuardInvoice
import YM.Integration.WilsonPositionScaleLawQinter

/-! The polynomial measured by the literal position Jacobian and the one
entered in the independent homogeneous invoice are the same full operator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardMeasured
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardInvoice (issue)
open WilsonPositionScaleLawGuardLift (pack)
open WilsonPositionScaleLawIndependent (B trial)
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Polynomial Classical BigOperators
variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "E"=>(Bel C.book).Field

include H in
theorem printed (d q:ℕ)(s g:ℝ):
    operator C (trial Z M ν d q s g)=issue C q (B Z M ν s d) (g:ℂ):=by
  ext v
  apply (fields C.labels d).injective
  change (fields C.labels d) ((fields C.labels d).symm
    (WilsonPhysicalPositionDiscreteBranches.field (trial Z M ν d q s g) ((fields C.labels d) v)))=_
  rw [LinearEquiv.apply_symm_apply,WilsonPositionScaleLawKinetic.field Z M H ν]
  let row (k:ℕ):Sec G d:=(g:ℂ)^k • (coeff k (B Z M ν s d)) ((fields C.labels d) v)
  change (∑k:Fin (q+1),row k.val)=_
  rw [Fin.sum_univ_eq_sum_range]
  dsimp only [row]
  rw [issue,WilsonPositionScaleLawGuardEval.printed]
  have I:Finset.Iic q=Finset.range (q+1):=by ext n;simp only [Finset.mem_Iic,Finset.mem_range];omega
  rw [I];simp only [_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl;intro k _
  rw [WilsonPositionScaleLawGuardLift.coefficient,WilsonPositionScaleLawGrade.reads]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
include H in
theorem original (d q:ℕ)(z:ℝ×Ratio):
    WilsonPositionScaleLawQinter.prediction Z M ν F J d q z=
      issue R.family q (B Z M ν (WilsonPositionScaleLawIndependent.time z.2) d) (WilsonPositionScaleLawKinetic.kinetic Z F J z.1:ℂ):=
  printed R.family Z M H ν d q _ _

end YM.Integration.WilsonPositionScaleLawGuardMeasured
