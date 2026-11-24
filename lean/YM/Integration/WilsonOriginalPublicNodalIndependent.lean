import YM.Integration.WilsonOriginalPublicPivotReflected
import YM.Integration.WilsonOriginalPublicNodalWord
import YM.Integration.WilsonOriginalPublicNodalOwners

/-! The independent regulator reads the measured vector with the exact weights
and the exact degree of the originally submitted occupied monomials. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1800000
namespace YM.Integration.WilsonOriginalPublicNodalIndependent
open Finset PowerSeries Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open XSpace ActualRunPhysicalPages PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerPositionTunedSlope (Columns paid finite)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicNodalOwners (home)
open WilsonOriginalPublicNodalWord (sheet)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOriginalPublicNodalFibre (complete)
open WilsonPositionProgramReportedField (entire)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[LinearOrder I](d:I→ℕ){h:I→ℕ}
    (κ:(j:I)→Knob (h j))(pt:I→Chamber){N p K:ℕ}(live:K≤N)(w:(j:I)→R.family.label (d j))
    (S:Finset I)(z:I→ Cover)(P:Period)(T:P.Tree)
local notation "δ" => (fun j:S=>d j)
local notation "roots" => (fun j:S=>z j)
local notation "g" => regulatorRun R.family N p K
local notation "e" => (fun j:S=>entire R (d j) K (N,p) (w j))
local notation "box" b:max => request R d (complete R d S b) (N:=N) (p:=p) (K:=K)
local notation "toll" c:max => WilsonOriginalPublicNodalFibre.change R d (N:=N) (p:=p) (K:=K) 1 S c
local notation "stamp" b:max => Kick.depthF univ δ b

include live in
theorem original (n:ℕ):
    coeff n (paid R δ (frozen R δ e) (finite R δ P roots T))=
      ∑c:Selection R d S,weight R d N p K w S c*
        coeff (n+stamp (home R d S c)) (sheet R d κ pt S z 1 c P T):=by
  have planted(b:Columns R δ):(∏j:S,e j (b j))*coeff (n+stamp b)
      (WilsonPositionProgramCopyTop.normalized R P δ roots b T)=
      ∑c:Selection R d S,((∏j:S,e j (b j))*(weight R d N p K (box b) S c*toll c))*
        coeff (n+stamp b) (sheet R d κ pt S z 1 c P T):=by
    rw [WilsonOriginalPublicNodalWord.filed R d κ pt (p:=p) live S b z 1 one_ne_zero P T,map_sum,mul_sum]
    apply sum_congr rfl
    intro c _
    simp only [coeff_smul,smul_eq_mul,mul_assoc]
  rw [WilsonPositionProgramTrialThermalGrades.coefficient]
  simp_rw [planted]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_eq_single (home R d S c)]
  · let b:=home R d S c
    have gp:(g:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ActualRunKernelPackets.regulator_pos R N p K live).ne'
    have refund:(∏j:S,e j (b j))*toll c=WilsonOriginalPublicTrialFigure.weight R δ g e b:=by
      rw [WilsonOriginalPublicNodalOwners.clock,
        ←WilsonPositionProgramTrialThermalGrades.restored R δ
          (ActualRunKernelPackets.regulator_pos R N p K live).ne' e b]
      change (_*(g:ℂ)^stamp b)*((g:ℂ)^stamp b)⁻¹=_
      rw [mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ gp),mul_one]
    have received:=WilsonOriginalPublicNodalOwners.received R d (p:=p) live w S c
    change ((_*(weight R d N p K (box b) S c*toll c))*_)=_
    rw [mul_comm (weight R d N p K (box b) S c),←mul_assoc (_:ℂ) (toll c),refund,received]
  · intro b _ diff
    rw [WilsonOriginalPublicNodalOwners.other R d (N:=N) (p:=p) (K:=K) S b c diff,zero_mul,mul_zero,zero_mul]
  · simp

def forecast (q:ℕ)(u:ℝ)(c:Selection R d S):ℂ:=
  ∑n∈Finset.Iic q,(u:ℂ)^n*coeff (n+stamp (home R d S c)) (sheet R d κ pt S z 1 c P T)

include live in
theorem valued (q:ℕ)(u:ℝ):
    WilsonOriginalPublicPivotReflected.evaluated q u (paid R δ (frozen R δ e) (finite R δ P roots T))=
      ∑c:Selection R d S,weight R d N p K w S c*forecast R d κ pt S z P T q u c:=by
  unfold WilsonOriginalPublicPivotReflected.evaluated
  simp only [original R d κ pt (p:=p) live w S z P T,mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun c _=>?_
  simp only [forecast,mul_sum]
  refine sum_congr rfl fun n _=>?_
  ring

end YM.Integration.WilsonOriginalPublicNodalIndependent
end
