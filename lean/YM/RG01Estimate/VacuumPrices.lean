import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-!
# The forced price really pays arbitrary powers after a single divisor

Local numerical inputs. No uniform lower bound on the Gaussian seed rate across stages is
assumed. `forecast` is a BEFORE-reset strong price, and `quoteHard` is not interchanged
with it: the capitalization test has to be used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate

open Function Filter Set Lattice Wilson RG Pressure MeasureTheory
open Push Push.AbsoluteSums SectorMeasure Oriented Shoot Precision
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Progress.DirectedRecipe PriceCompiler Org Input Supply Time
open PhysicalNext PhysicalNext.Repeat Roost ThroughLaunch
open ConnectedActivityE6 Reserves
open scoped Topology BigOperators Classical

variable {G : Gauge}

namespace VacuumPrices

lemma strong_le_budget {B : ℕ} {w a b κ : ℝ} (h : Payments.Rates B w a b κ) : a ≤ w := by
  let e := Payments.inflation a b κ
  have he : Real.exp κ * a ≤ e := le_add_of_nonneg_right (mul_nonneg zero_le_two h.soft)
  have hf : e ≤ Real.exp e - 1 := by linarith only [Real.add_one_le_exp e]
  apply le_trans _ h.returns
  change a ≤ Real.exp (-κ) * (Real.exp e - 1)
  rw [Real.exp_neg]
  apply le_trans _ (mul_le_mul_of_nonneg_left (he.trans hf) (inv_pos.mpr (Real.exp_pos _)).le)
  rw [inv_mul_cancel_left₀ (Real.exp_pos _).ne']

variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (R : Factor A)

/-- A pre-reset forced hit cap calibrated on any in-band fine beta, bounded by the
actual *coarse* forced allowance. -- This uses the booked Pairing cutoffs; it is
not just the inequality of two display exponentials at fixed stage costs. -/
lemma forecast_allowance {m N : ℕ} (hm : m < N) {β : ℝ} (hb : β ∈ Shoot.band A.B.a (m+1)) :
    Time.forecastK A.B.a m R.scout β ≤ A.B.a.clock.forcedAllowance m := by
  let a := A.B.a
  let u := a.clock.hatBeta m
  let y := a.clock.hatBeta (m+1)
  let j := a.clock.J (m+1)
  let i := a.clock.J m
  let k := a.budget m
  obtain ⟨-, _, _, _, hE, _, ht⟩ := Deployment.clock_eqns a.clock m
  have hs := R.machine.shops j u (A.B.valid.pays m) i (step_paid a m)
  have hj : M.p.profile i = a.params m := (params_eq A.B.valid m).symm
  have ha : Time.Same (a.params m) k := ⟨rfl,rfl,rfl⟩
  obtain ⟨-, -, hK⟩ := hs k (hj.symm ▸ ha) rfl ht
  have hy : y = u + G.slopeConstant*Real.log (D.L j).val := by
    rw [← PriceCompiler.block_eq A.B.valid]; exact (Deployment.hat m).symm
  have hm' := hK (R.exchange j i) (A.B.kin.alpha N m) (a.clock.theta j) β
    (UVNext.CouplingReset.within_alpha hm) (hy ▸ trial_in hb)
  obtain ⟨_, _, hFees, hFine⟩ := hm'
  obtain ⟨_, _, _, hRates⟩ := hFees.hard
  have hh := le_trans (strong_le_budget hRates) (hFine (R.machine.coverage j i (step_paid a m)).1).2
  rw [← hy] at hh
  change Time.forecastK a m R.scout β ≤ a.clock.forcedAllowance m
  rw [hE]
  exact hh

-- pay x in probe u
lemma poly_ge (ε : ℝ) (he : 0 < ε) (d : ℕ) : 1 ≤ Reserves.polyPrice ε d := by
  have h := polynomial_cost he (show (0:ℝ)≤0 from le_rfl) d
  simpa only [add_zero, one_pow, mul_zero, Real.exp_zero, mul_one, Reserves.polyPrice] using! h

variable {L : Side} {P : Teller G} (Q : ConnectedActivityE6.Target G P)

/-- `armK` is at least this amount at every paid order. Thus an *upper*
bound on `armK` proves a lower bound on the seed fugacity. -/
lemma buys_seed (t : ℝ) (x μ : ℝ) (n : ℕ) (hx : 1 ≤ betaF G x L) (ht : t ≤ (Real.sqrt (betaF G x L))⁻¹) :
    Real.exp (-Q.mark L μ x) * t ≤ Cash.armK Q L μ x 0 n := by
  let s:= betaF G x L
  have hs : 0 < s := zero_lt_one.trans_le hx
  have hv : (Real.sqrt s)⁻¹ ≤ Q.goal L x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le]
    exact Real.rpow_le_rpow_of_exponent_le hx Q.start.le
  have hh : Q.goal L x ≤ Q.overture L μ x n := by
    unfold ConnectedActivityE6.Target.overture ConnectedActivityE6.Target.quantum Mixed.Costs.ceiling
    unfold Reserves.extract Reserves.treeYield
    dsimp only [ConnectedActivityE6.Target.costs, Buy.quote]
    norm_num
    have he := poly_ge _ Q.usable n
    have hg : 0 ≤ Q.goal L x := Real.rpow_nonneg hs.le _
    nlinarith only [he,hg, Real.exp_pos (-(Delay.hatWin G L (μ/2) (1/2) x) / 4)]
  let a:= Q.overture L μ x n
  have hp : 0 ≤ a := (Q.overture_pos x n hs).le
  have h1 : t ≤ a := ht.trans (hv.trans hh)
  unfold Cash.armK
  norm_num
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  unfold ConnectedActivityE6.Target.mergeScale
  linarith

end VacuumPrices
end YM.RG01Estimate
