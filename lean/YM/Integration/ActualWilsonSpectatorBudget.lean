import YM.Integration.ActualWilsonSpectatorDifference
import YM.Integration.ActualWilsonAxisSpectator

/-! Covered vacuum budgets for the two spectator factors on the actual
regulator. The signed retained singleton still uses its own support bill. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonSpectatorBudget

open Function Set Filter Finset Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid SectorNext.Vacuum CoveredOrdinaryInsertion Push.AbsoluteSums
open Comparison.RG02 LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained RG3.Script.Picnic
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open ActualWilsonForcedSlots ActualWilsonAxisSpectator
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- The entire absolute sum of scalar pinned vacuum minors costs one,
uniformly in the volume, address and external configuration. -/
theorem coat_budget_one {p : BudgetPoint} {w : ℝ} {X : Rep G n}
    (hX : X.activities.KBound p w) (hw : w ≤ 1) (i : ℕ) (U : Config G n) :
    SumBudget (fun s : Finset ℕ => ‖coat X i s U‖) 1 := by
  obtain ⟨k,hk,hpay⟩ := hX
  let K (j : ℕ) := (X.activities.forced j).support
  let Z (j : ℕ) := (X.activities.forced j).inventory
  let D := flags X.p.threshold U
  have hit (x : Site n) (I : Finset ℕ) : (∑ j ∈ I, if x ∈ Z j then k j else 0) ≤ w := by
    apply le_trans _ (budget_sum (hpay x) I)
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : x ∈ Z j
    · rw [if_pos hz, if_pos ((X.activities.forced j).inventory_sup hz)]
      exact p.loMass _ _ (hk j).1
    rw [if_neg hz]
    split
    · exact (hk j).1.trans (p.loMass _ _ (hk j).1)
    exact le_rfl
  let e (j : ℕ) : ℝ := if j = i then 1 else 0
  have he : SumBudget e 1 := by
    apply budget_of_sum
    · intro j
      dsimp only [e]
      split <;> norm_num
    intro s
    dsimp only [e]
    rw [sum_ite_eq']
    split <;> norm_num
  have H := insertion_budget K Z (fun j => (X.activities.forced j).inventory_sup)
    (fun j => (X.activities.forced j).inventory_ne) hw k (fun j => (hk j).1) hit e he D
  have hinst : (fun a b : ℕ => Classical.propDecidable (a = b)) =
      instDecidableEqNat := Subsingleton.elim _ _
  rw [hinst] at H
  apply budget_mono H (fun _ => norm_nonneg _)
  intro s
  have hA : accounted K Z D s ↔ X.activities.admissible X.p U s := by
    apply iff_of_eq
    unfold accounted Activities.admissible K Z D
    congr!
  simp only [e, ite_mul, one_mul, zero_mul, sum_ite_eq', hA]
  by_cases hI : i ∈ s <;> by_cases ha : X.activities.admissible X.p U s
  · simp only [coat, hI, ha, and_self, if_true, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun j _ => (Complex.norm_real _).trans_le ((hk j).2 U))
  all_goals simp [coat,hI,ha]

theorem dressed_le_one {p : BudgetPoint} {w : ℝ} {X : Rep G n}
    (hX : X.activities.KBound p w) (hw : w ≤ 1) (i : ℕ) (U : Config G n) :
    ‖dressed X i U‖ ≤ 1 := by
  have h := coat_budget_one hX hw i U
  exact (norm_tsum_le_tsum_norm h.2.1).trans h.2.2

/-- The actual two-exponential signed spectator series has a weighted
absolute bill. Each retained signed row occurs once, also when several
rows share the same footprint. -/
theorem paired_price {X Y : Rep G n} {pX pY : BudgetPoint} {wX wY : ℝ}
    (hX : X.activities.KBound pX wX) (hY : Y.activities.KBound pY wY)
    (hx : wX ≤ 1) (hy : wY ≤ 1) {d : ℕ} {F : Frame G d}
    (q : Coefficient F n) {o : Site n} {κ r : ℝ} (hr : q.remBound o X κ r)
    (e : ℕ → ℕ) (U : Config G n) :
    let α := Real.exp (X.exponent U)
    let β := Real.exp (Y.exponent U)
    SumBudget (fun j => X.p.mass (X.activities.forced j).support
      ‖q.forced j U * ((α : ℂ) * dressed X j U - (β : ℂ) * dressed Y (e j) U)‖)
      ((α+β)*(κ*r)) := by
  intro α β
  obtain ⟨a,b,ha,_,hab,hκ,_,z,hz,hr⟩ := hr
  have h0 : 0 ≤ α+β := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have H := budget_scale h0 (budget_loosen hz
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left ha).trans hab) hκ.le))
  apply budget_mono H (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  intro j
  have hj : ‖(α : ℂ) * dressed X j U - (β : ℂ) * dressed Y (e j) U‖ ≤ α+β := by
    apply (norm_sub_le ..).trans
    rw [norm_mul,norm_mul,Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact add_le_add (mul_le_of_le_one_right (Real.exp_pos _).le (dressed_le_one hX hx j U))
      (mul_le_of_le_one_right (Real.exp_pos _).le (dressed_le_one hY hy (e j) U))
  rw [norm_mul]
  calc
    _ ≤ Real.exp (X.p.supportExponent * coverNumber X.p.B (X.activities.forced j).support) *
        (z j * (α+β)) := mul_le_mul_of_nonneg_left
          (mul_le_mul ((hr j).2 U) hj (norm_nonneg _) (hr j).1) (Real.exp_pos _).le
    _ = _ := by unfold BudgetPoint.mass; ring

/-- At every paid level on a fixed Wilson run the whole physical signed
difference has the divided singleton bill times the two actual vacuum
exponentials. This holds for every period, cutoff, test and external field. -/
theorem selected (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {delta : ℝ} {forcedOrder : ℕ}
    (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period)) :
    let C := R.family
    let i := datum.level
    let W := C.path.rep datum.cutoff datum.period i
    let X := S.output.carrier.rep
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (i+1)
    let r := F.kernelCosts v*g^forcedOrder/F.outputRadii v
    let e := address X (OriginalForcedAddresses.actual_keeper R hG datum.cutoff i datum.period datum.below.le)
    let f j := (D.contents.each j U).part (B.fire v) *
      ((Real.exp (X.exponent U) : ℂ) * dressed X j U -
        (Real.exp (W.exponent U) : ℂ) * dressed W (e j) U)
    let cap := (Real.exp (X.exponent U) + Real.exp (W.exponent U)) * (forcedDivisor C i*r)
    SumBudget (fun j => X.p.mass (X.activities.forced j).support ‖f j‖) cap ∧
      ‖spectator R hG S x v U‖ ≤ cap := by
  intro C i W X D g r e f cap
  obtain ⟨q,_,_,hq,_,hr⟩ := ActualWilsonResidualCoefficient.selected S H v hreserve x
  have hrow (j : ℕ) : q.forced j U = (D.contents.each j U).part (B.fire v) := by
    rw [hq]
    exact (ActualWilsonForcedRow.each_solution D v j U
      (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U)).symm
  have hclock := (eventually_atTop.1 (actual_forced_smallness C hG R.makes (Fintype.card V))).choose_spec
    i hLate datum.cutoff datum.period datum.below 0
  have hw : C.path.levels.clock.forcedAllowance i ≤ 1 := by
    apply (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg (Fintype.card V))
      H.residual_price.budget.divisor.le)).trans
    simpa only [pow_zero,mul_one] using hclock
  have hW : W.activities.KBound W.p (C.path.levels.clock.forcedAllowance i) :=
    (R.makes.wilson.represents datum.cutoff datum.period i datum.below.le).good.labels.boundK
  have HB := paired_price S.actual_forced hW hw hw q hr e U
  have Hpaid : SumBudget (fun j => X.p.mass (X.activities.forced j).support ‖f j‖) cap := by
    simpa only [hrow, f, cap] using HB
  have Hroot := budget_mono Hpaid (fun j => norm_nonneg (f j))
    (fun j => X.p.loMass _ _ (norm_nonneg (f j)))
  exact ⟨Hpaid,(norm_tsum_le_tsum_norm Hroot.2.1).trans Hroot.2.2⟩

end YM.Integration.ActualWilsonSpectatorBudget
