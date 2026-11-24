import YM.Integration.WilsonIndependentConditionedFolioPoles

/-! Resolve the genuine fitted sum into its normalized public columns, including the unit. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioWeights
open Function Finset Lattice Wilson RG Source Labels Laurent Pert.Asymptotics
open ActualRunPhysicalPages PhysicalNext.Repeat.Legato
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet ticket seats)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalPublicNodalCanonical (request)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I](R:Run G)(d:I→ℕ)(N per K:ℕ)
    (w:(i:I)→R.family.label (d i))(S:Finset I)
local notation "g_" => (regulatorRun R.family N per K:ℂ)
local notation "B_" b:max => seats R d S b
local notation "w_" b:max => request R d (B_ b) (N:=N) (p:=per) (K:=K)
def payment (b:Columns R (fun i:S=>d i)):ℂ:=∏i:S,entire R (d i) K (N,per) (w i) (b i)
def height (b:Columns R (fun i:S=>d i)):ℕ:=∑i:S,((R.family.labels.level (d i)).grades (b i)).2

omit [DecidableEq I] in
theorem printed (b:Columns R (fun i:S=>d i)):
    packet R d S w N per K b=payment R d N per K w S b*(g_^(height R d S b))⁻¹:=by
  unfold packet payment height WilsonOriginalPublicTrialFigure.amount
  push_cast
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_inv_distrib,←Finset.prod_mul_distrib]

theorem original [Fintype I](kn:K≤N)(q:Selection R d S):
    weight R d N per K w S q=∑b:Columns R (fun i:S=>d i),payment R d N per K w S b*ticket R d S (w_ b) N per K q:=by
  classical
  let n:=degree R d S (fill R d S q)
  have gg:g_≠0:=Complex.ofReal_ne_zero.mpr (ActualRunKernelPackets.regulator_pos R N per K kn).ne'
  have prod (b:Columns R (fun i:S=>d i)):
      WilsonOlderFreshSoftSocketFaces.cash R d (B_ b) S N per K q=ticket R d S (w_ b) N per K q:=rfl
  have earned:=WilsonOlderFreshSoftSocketMeasuredCash.original R d S w (per:=per) kn q
  rw [WilsonOlderFreshSoftSocketTotal.priced] at earned
  calc
    _=(∑b:Columns R (fun i:S=>d i),packet R d S w N per K b*(ticket R d S (w_ b) N per K q))*g_^n:=by
      simp only [←prod]
      rw [earned,mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ gg),mul_one]
    _=_:=by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h:n=height R d S b
      · rw [printed,h]
        have h₀:=pow_ne_zero (height R d S b) gg
        field_simp
      · have fees:∑i:S,((R.family.labels.level (d i)).grades ((B_ b) i)).2=height R d S b:=by
          unfold height
          apply Finset.sum_congr rfl
          intro i _
          rw [show (B_ b) i=b i from dif_pos i.property]
        have wrong:degree R d S (fill R d S q)≠∑i:S,((R.family.labels.level (d i)).grades ((B_ b) i)).2:=by rwa [fees]
        rw [(WilsonIndependentConditionedFolioPoles.marked R d (B_ b) N per K S q wrong).2,mul_zero,zero_mul,mul_zero]

end YM.Integration.WilsonIndependentConditionedFolioWeights
end
