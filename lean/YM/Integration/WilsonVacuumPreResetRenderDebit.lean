import YM.Integration.WilsonVacuumPreResetRenderReserve

/-! The prepaid reporting amount is spent on the complete genuine original
per-row quote, with its real field threshold and signed input coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderDebit
open Function Filter Finset Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset Collection
open Next.Scheduling Extra.Iteration PhysicalNext.Repeat.Legato
open RG.Shoot WilsonStartup Progress.DirectedRecipe
open WilsonVacuumPreResetRenderReserve
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem moment (d:ℕ){σ w:ℝ}(pos:0<σ)(floor:1 ≤ w)(width:σ⁻¹ ≤ w):
    0 ≤ momentCost d σ ∧ momentCost d σ ≤ FundedCloverWidthMoment.coefficient d*w^(d+2):=by
  let s:=min σ 1
  have sp:0<s:=lt_min pos zero_lt_one
  have charge:=FundedCloverWidthMoment.price d sp (min_le_right σ 1)
  have inv:s⁻¹ ≤ w:=by
    by_cases h:σ ≤ 1
    · simpa [s,min_eq_left h] using width
    · simpa [s,min_eq_right (le_of_not_ge h)] using floor
  have lean:momentCost d σ ≤ momentCost d s:=by
    apply (decay_summable d (σ/4) (by positivity)).tsum_le_tsum _ (decay_summable d (s/4) (by positivity))
    intro n
    unfold decay
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have ss:s ≤ σ:=min_le_left _ _
    nlinarith only [mul_nonneg (sub_nonneg.mpr ss) (Nat.cast_nonneg n : (0:ℝ)≤n)]
  exact ⟨tsum_nonneg (fun n=>by unfold decay;positivity), lean.trans (charge.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr sp.le) inv _) (FundedCloverWidthMoment.coefficient_nonneg d)))⟩

def rose (B:BudgetPoint)(a:PrismA G):ℝ:=
  if a.rise=0 then (1+bloom G B)*Real.exp (81*B.supportExponent) else 1

theorem formula (B:BudgetPoint)(σ C:ℝ)(a:PrismA G):
    let k:=a.rise+2
    FundedCorrectedPeriod.credit B σ C a=
      Frame.cost B* |factor| *rose B a*Wages.startup G k B.power B.order*
      Real.exp (B.supportExponent*(1+2*(k:ℝ)))*momentCost (Wages.grade k B.power B.order) σ*
      B.threshold^k*C:=by
  intro k
  by_cases hr:a.rise=0
  · simp [FundedCorrectedPeriod.credit,hr,k,rose,Frame.roseCharge,Frame.alto,Wages.fund]
    ring
  · simp [FundedCorrectedPeriod.credit,hr,k,rose,Wages.fund]
    ring

theorem original (T:RG.Stage)(B:BudgetPoint)(order:B.order=T.order)(power:B.power=T.power)
    (exponent:B.supportExponent ≤ T.supportExponent+6)(x σ C:ℝ)(pos:0<σ)(clock:1 ≤ 2*Real.log x)
    (width:σ⁻¹ ≤ 2*Real.log x)(a:PrismA G):
    |FundedCorrectedPeriod.credit B σ C a| ≤ amount G T (a.rise+2) x*B.threshold^(a.rise+2)* |C|:=by
  let P:=Time.probe T
  let A:=T.supportExponent+6
  let k:=a.rise+2
  let h:=Wages.grade k T.power T.order
  have sameCost:Frame.cost B=Frame.cost P:=by simp [Frame.cost,turnFee,P,Time.probe,order,power]
  have sameBloom:bloom G B=bloom G P:=by simp [bloom,P,Time.probe,order,power]
  have roseLe:|rose B a| ≤ (1+|bloom G P|)*Real.exp (81*A):=by
    by_cases q:a.rise=0
    · rw [rose,if_pos q,sameBloom,abs_mul,abs_of_nonneg (Real.exp_nonneg _)]
      have hb:|1+bloom G P| ≤ 1+|bloom G P|:=by simpa using abs_add_le (1:ℝ) (bloom G P)
      gcongr
    · rw [rose,if_neg q,abs_one]
      have ha:0 ≤ 81*A:=by dsimp [A]; linarith [T.price_pos]
      exact one_le_mul_of_one_le_of_one_le (by linarith [abs_nonneg (bloom G P)]) (Real.one_le_exp ha)
  have rising:Real.exp (B.supportExponent*(1+2*(k:ℝ))) ≤ Real.exp (A*(1+2*(k:ℝ))):=by
    gcongr
  have money:=moment h pos clock width
  rw [formula]
  simp only [abs_mul,abs_abs,abs_of_nonneg (Real.exp_nonneg _),sameCost,order,power,
    abs_of_nonneg (pow_nonneg B.threshold_pos.le _)]
  rw [show |momentCost (Wages.grade (a.rise+2) T.power T.order) σ| = momentCost _ σ from abs_of_nonneg money.1]
  let rr:=(1+|Frame.cost P|)*(1+|factor|)*((1+|bloom G P|)*Real.exp (81*A))*
    (1+|Wages.startup G k T.power T.order|)*Real.exp (A*(1+2*(k:ℝ)))*
    (FundedCloverWidthMoment.coefficient h*(2*Real.log x)^(h+2))*B.threshold^k* |C|
  have billed:|Frame.cost P| * |factor| * |rose B a| * |Wages.startup G k T.power T.order| *
        Real.exp (B.supportExponent*(1+2*(k:ℝ)))*momentCost h σ*B.threshold^k* |C| ≤ rr:=by
    dsimp only [rr]
    have th:0≤B.threshold:=B.threshold_pos.le
    gcongr <;> first | exact money.2 | exact roseLe | exact rising | positivity | linarith
  apply billed.trans_eq
  dsimp [rr,amount,base,k,h,P,A]
  ring

end YM.Integration.WilsonVacuumPreResetRenderDebit
