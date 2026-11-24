import YM.Integration.ActualWilsonPhysicalDefect
import YM.Push.GRID_APPROXIMATION.Hit

/-! Distance from the prescribed physical mark to the genuine forced inventories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonRootDistance
open Function Filter Set Finset Lattice Lattice.Corona Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained Comparison.RG02
open PhysicalNext.Repeat.Legato Extra.Histories SectorNext.Vacuum Push.AbsoluteSums ActualWilsonAxisSpectator ActualWilsonSpectatorDifference
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

/-- Every measured flag lies at least this many native block legs from the indicated root. -/
def Remote (B : ℕ) (θ : ℝ) (o : Site n) (r : ℕ) (U : Config G n) : Prop :=
  ∀ z ∈ flags θ U, r ≤ separation o z/Push.GridApprox.Attach.leg B

theorem covers (B : ℕ) {θ : ℝ} {o : Site n} {r : ℕ} {U : Config G n} {a : ForcedAddress G n}
    (hfar : Remote B θ o r U) (ho : o∈a.support) (ha : a.eligible θ U) :
    r≤coverNumber B a.support := by
  obtain ⟨z,hz⟩ := a.inventory_ne
  have hz' : z∈a.support ∩ flags θ U := ha.1.symm ▸ hz
  exact (hfar z (mem_inter.mp hz').2).trans (Push.GridApprox.Attach.distance_charge a.support B o z ho (a.inventory_sup hz))

variable {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {C : Family G} {J : Request V}
    {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    {δ : ℝ} {a : ℕ}

theorem selected (S : Chosen K I M) (H : Bounds S δ a)
    (hreserve : (C.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (U : Config G (C.side datum.level datum.period)) (r : ℕ)
    (hfar : Remote (A.outputNorm datum.level).B S.output.carrier.rep.p.threshold (F.coarseRoots v) r U)
    (c : ℕ → ℂ) (hc : ∀ j, ‖c j‖≤1) :
    let p := A.outputNorm datum.level
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let y j := (D.contents.each j U).part (B.fire v)
    let fee := F.kernelCosts v*(forcedDivisor C datum.level*Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1)^a/F.outputRadii v)
    let bill := Real.exp (-p.supportExponent*r)*fee
    SumBudget (fun j => ‖y j*c j‖) bill ∧ ‖∑' j,y j*c j‖≤bill := by
  intro p D y fee bill
  obtain ⟨q,_,_,hq,hformat,_⟩ := ActualWilsonResidualCoefficient.selected S H v hreserve x
  have hy (j : ℕ) : y j=q.forced j U := by
    rw [hq]
    exact ActualWilsonForcedRow.each_solution D v j U (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U)
  obtain ⟨t,ht,hpaid⟩ := ActualWilsonForcedRow.retained S H v
  let decay := Real.exp (-p.supportExponent*r)
  have hd : 0≤decay := (Real.exp_pos _).le
  have hbill : SumBudget (fun j => ‖y j*c j‖) bill := by
    apply budget_mono (budget_scale hd hpaid) (fun j => norm_nonneg _)
    intro j
    by_cases hz : y j=0
    · rw [hz,zero_mul,norm_zero]
      exact mul_nonneg hd (hpaid.1 j)
    have hqj : q.forced j U≠0 := (hy j) ▸ hz
    have hfun : q.forced j≠0 := fun h => hqj (congrFun h U)
    let s := (S.output.carrier.rep.activities.forced j).support
    have hn : r≤coverNumber p.B s := covers p.B hfar (hformat.carried j hfun) (hformat.forcing j U hqj)
    have hr : (r:ℝ)≤(coverNumber p.B s:ℝ) := by exact_mod_cast hn
    have hpos : 0≤ -p.supportExponent*r+p.supportExponent*coverNumber p.B s := by
      nlinarith only [mul_nonneg p.exponent_pos.le (sub_nonneg.mpr hr)]
    have hm : t j≤decay*p.mass s (t j) := by
      dsimp only [decay,BudgetPoint.mass]
      rw [←mul_assoc,←Real.exp_add]
      exact le_mul_of_one_le_left (ht j).1 (Real.one_le_exp hpos)
    apply le_trans _ hm
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg _) (hc j)).trans
    rw [hy,hq]
    exact (ht j).2 x U
  exact ⟨hbill,(norm_tsum_le_tsum_norm hbill.2.1).trans hbill.2.2⟩

theorem wilson (R : Run G) (hG : G.Simple) {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {Y : Bulk.Chain R.family.path} {K : NumericPrices A} {F : AnalyticInput J A datum}
    {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) (H : Bounds S δ a)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent≤J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) (r : ℕ)
    (hfar : Remote (A.outputNorm datum.level).B S.output.carrier.rep.p.threshold (F.coarseRoots v) r U) :
    let C := R.family
    let W := C.path.rep datum.cutoff datum.period datum.level
    let e := ActualWilsonForcedSlots.address S.output.carrier.rep
      (OriginalForcedAddresses.actual_keeper R hG datum.cutoff datum.level datum.period datum.below.le)
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let b j := (D.contents.each j U).part (B.fire v)*dressed W (e j) U
    let fee := F.kernelCosts v*(forcedDivisor C datum.level*Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1)^a/F.outputRadii v)
    let bill := Real.exp (-(A.outputNorm datum.level).supportExponent*r)*fee
    SumBudget (fun j => ‖b j‖) bill ∧ ‖∑' j,b j‖≤bill := by
  intro C W e D b fee bill
  apply selected S H hreserve x v U r hfar (fun j => dressed W (e j) U)
  intro j
  have hW := R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  apply ActualWilsonSpectatorBudget.dressed_le_one hW.good.labels.boundK _ (e j) U
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))

end YM.Integration.ActualWilsonRootDistance
