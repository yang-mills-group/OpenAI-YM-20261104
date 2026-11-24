import YM.Integration.WilsonOriginalThermometerTollBudget
import YM.Integration.WilsonMeasuredSemesterSubpower
/-! Repricing one genuinely received colour at one of its own original measured
edges.  The bound on the posted radius uses its original restamping multiplier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOneColorRadius
open Lattice RG Wilson Push.AbsoluteSums QuadraticLocal QuadraticLocal.Advent Filter RG.Supply PhysicalNext PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonLimitConstruction WilsonCoeffUV WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open scoped BigOperators Topology
variable {G:Gauge}

private theorem currency {H B n w Ω h H' : ℝ} (late:32≤H)
    (band:H/2≤B) (next:H'≤2*H) (hp:0<h) (hn:0<n) (wp:0<w) (op:0<Ω)
    (upper:w⁻¹≤2*H'*n) (reserve:Ω^6≤H') (step:h≤2*H^2) :
    ((Real.sqrt B)⁻¹)^12/n≤w/(Ω^6*h) :=by
  have Hpos:0<H:=by linarith
  have Bpos:0<B:=by linarith
  have H'_pos:0<H':=(pow_pos op 6).trans_le reserve
  have dx : w⁻¹*Ω^6*h≤((4*H*n)*(2*H))*(2*H^2):=by
    apply mul_le_mul _ step hp.le (by positivity)
    exact mul_le_mul (upper.trans (mul_le_mul_of_nonneg_right (by linarith only [next]) hn.le))
      (reserve.trans next) (pow_nonneg op.le _) (by positivity)
  have f0 : 16*H^4≤B^6:=by
    have hB:16≤B:=by linarith
    have sqB:256≤B^2:=by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (show 0≤B+16 by positivity)]
    calc
      _ ≤ 16*(2*B)^4:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Hpos.le (by linarith only [band]) 4) (by norm_num)
      _ = 256*B^4:=by ring
      _ ≤ B^2*B^4:=mul_le_mul_of_nonneg_right sqB (pow_nonneg Bpos.le _)
      _ = B^6:=by ring
  have funded:w⁻¹*Ω^6*h≤B^6*n:=dx.trans (by
    calc
      _ = 16*H^4*n:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right f0 hn.le)
  have g : ((Real.sqrt B)⁻¹)^12=(B^6)⁻¹:=by
    rw [inv_pow]
    congr 1
    calc
      _=((Real.sqrt B)^2)^6:=by ring
      _=B^6:=by rw [Real.sq_sqrt Bpos.le]
  rw [g]
  calc
    _=(B^6*n)⁻¹:=by simp [div_eq_mul_inv,mul_comm]
    _≤(w⁻¹*Ω^6*h)⁻¹ := by simpa only [one_div] using (one_div_le_one_div_of_le
      (mul_pos (mul_pos (inv_pos.mpr wp) (pow_pos op 6)) hp) funded)
    _=w/(Ω^6*h):=by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring

theorem original (R:Run G) (simple:G.Simple) :
    ∀ᶠ i:ℕ in atTop, ∀ N per, i≤N →
    ∀ {j:ℕ}, i=j+1 → ∀ {w n Ω h C:ℝ}, 0<w → 0<n → 0<Ω → 0<h →
    w⁻¹≤2*R.family.path.levels.clock.hatBeta (i+1)*n →
    Ω^6≤R.family.path.levels.clock.hatBeta (i+1) → C≤2 →
    h ≤ max 1 (max (budgetR R j*budgetR R i) C) →
    (regulatorRun R.family N per i)^12/n≤w/(Ω^6*h):=by
  let A:=R.family.path.levels
  have rise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually_ge_atTop 32, RG01.Physical.nextHat simple A] with i late follow
  intro N per before j hj w n Ω h C wp np op hp enter fee Cb receipt
  have pos:0<A.clock.hatBeta i:=by linarith only [late]
  have adj: A.clock.hatBeta (i+1)≤2*A.clock.hatBeta i:=by linarith only [follow]
  have b0:budgetR R j≤A.clock.hatBeta i:=hj ▸ WilsonOriginalThermometerTollBudget.parameter R j
  have b1:budgetR R i≤2*A.clock.hatBeta i:=(WilsonOriginalThermometerTollBudget.parameter R i).trans adj
  have multiply:=mul_le_mul b0 b1 (zero_le_one.trans (budget_pos (R:=R) (i:=i))) pos.le
  have step:h≤2*(A.clock.hatBeta i)^2:=receipt.trans (max_le (by nlinarith [late,pos]) (max_le
    (by nlinarith only [multiply]) (by nlinarith [Cb, late,pos])))
  exact currency late (R.makes.wilson.represents N per i before).band.1 adj hp np wp op enter fee step

end YM.Integration.WilsonMeasuredOneColorRadius
end
