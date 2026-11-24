import YM.Integration.ActualWilsonSpectatorBudget
import YM.Integration.CoveredOrdinaryMinor
import YM.Planned.ATOM_FORCED_ESTIMATE.Outside

/-! Compulsory coverage by the genuine Wilson vacuum outside an arbitrary puncture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonExteriorPrice
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato SectorNext.Vacuum Push.AbsoluteSums Planned.Forced
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def fee (p : BudgetPoint) (w : ℝ) (D : Support n) : ℝ :=
  (if D=∅ then 1 else w)*Real.exp (-flagRate p * D.card)

theorem covered (A : Activities G n) {p : BudgetPoint} {w : ℝ} (H : A.KBound p w)
    (hw : w ≤ 1) (T : Support n) (U : Config G n) :
    SumBudget (fun J => ‖outsideTerm A p T U J‖) (fee p w (flags p.threshold U \ T)) ∧
       ‖outsideGas A p T U‖ ≤ fee p w (flags p.threshold U \ T) := by
  obtain ⟨v,hv,hpaid⟩ := H
  let K (j : ℕ) := (A.forced j).support
  let Z (j : ℕ) := (A.forced j).inventory
  let D := flags p.threshold U \ T
  have hit (o : Site n) (I : Finset ℕ) :
      (∑ j ∈ I, if o ∈ Z j then v j*Real.exp (flagRate p*(Z j).card) else 0) ≤ w := by
    apply le_trans _ (budget_sum (hpaid o) I)
    apply sum_le_sum
    intro j _
    by_cases h : o ∈ Z j
    · rw [if_pos h, if_pos ((A.forced j).inventory_sup h)]
      unfold BudgetPoint.mass
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (inventory_pay p (A.forced j).inventory_sup)) (hv j).1
    · rw [if_neg h]
      exact (hpaid o).1 j
  have H := CoveredOrdinaryMinor.covered_budget K Z (fun j => (A.forced j).inventory_sup)
    (fun j => (A.forced j).inventory_ne) hw v (fun j => (hv j).1) hit D
  have hd (J : Finset ℕ) : ‖outsideTerm A p T U J‖ ≤
      if accounted K Z D J then ∏ j ∈ J,v j else 0 := by
    by_cases h : ExteriorOK A p T U J
    · have hA : accounted K Z D J := by
        refine ⟨h.1,Finset.ext fun z => ?_⟩
        simpa only [Finset.mem_biUnion,Push.Local.flagsFor,Z,D,Finset.mem_sdiff] using Finset.ext_iff.mp h.2.2 z
      rw [outsideTerm,if_pos h,if_pos hA,norm_prod]
      exact prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => (hv j).2 U)
    · rw [outsideTerm,if_neg h,norm_zero]
      exact H.1 J
  have hp := budget_mono H (fun j => norm_nonneg (outsideTerm A p T U j)) hd
  exact ⟨hp,(norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2⟩

theorem selected (R : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M)
    (T : Support (R.family.side datum.level datum.period)) (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let P := C.path.levels.budget i
    let W := C.path.rep datum.cutoff datum.period i
    let X := S.output.carrier.rep
    let w := C.path.levels.clock.forcedAllowance i
    let cap := fee P w (flags P.threshold U \ T)
    SumBudget (fun J => ‖outsideTerm X.activities X.p T U J‖) cap ∧
      SumBudget (fun J => ‖outsideTerm W.activities W.p T U J‖) cap ∧
       ‖outsideGas X.activities X.p T U‖ ≤ cap ∧ ‖outsideGas W.activities W.p T U‖ ≤ cap := by
  intro C i P W X w cap
  have hw : w ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hx : X.p=P := S.output.carrier.point
  have hy : W.p=P := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).vac
  have hX := covered X.activities S.actual_forced hw T U
  have hW0 : W.activities.KBound W.p w := (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have hW : W.activities.KBound P w := hy ▸ hW0
  rw [hx,hy]
  exact ⟨hX.1,(covered W.activities hW hw T U).1,hX.2,(covered W.activities hW hw T U).2⟩

end YM.Integration.ActualWilsonExteriorPrice
