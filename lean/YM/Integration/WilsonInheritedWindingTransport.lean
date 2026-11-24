import YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedInput
import YM.Integration.WilsonMeasuredWindingSum
import YM.WilsonCoeffUV.Vacuum.UV.RatioLimit

/-! Downward transport of a winding packet already born at its charged Wilson date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInheritedWindingTransport
open Filter Lattice RG PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonLimitConstruction.FundedInheritedMarkedInput
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem band (L : Levels G) (simple : G.Simple) (T : Credit) :
    ∀ᶠ i : ℕ in atTop, ∀ b ≥ i,
      (T.buy (zz L i + (L.S.scale b-L.S.scale i) + ((b-i : ℕ) : ℝ)))^(b-i) ≤
      WilsonMeasuredWindingSum.room L (((T.d+1 : ℕ) : ℝ)/Real.log 3) b := by
  let c := G.slopeConstant
  let h := Real.log 3
  let B := 1+(1+h⁻¹)*c⁻¹
  have hc : 0<c := G.slopeConstant_pos simple
  have hh : 0<h := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have mono := WilsonStartup.Timing.hat_mono L hc.le
  filter_upwards [(WardBin.bell L simple).eventually_ge_atTop
    (max (Real.exp 1) (T.x*B^T.d))] with i hi b hib
  let H := L.clock.hatBeta b
  have e1 : Real.exp 1 ≤ L.clock.hatBeta i := (le_max_left ..).trans hi
  have lb : T.x*B^T.d ≤ H := (le_max_right ..).trans (hi.trans (mono hib))
  have one : 1 ≤ Real.log (L.clock.hatBeta i) := by
    simpa using Real.log_le_log (Real.exp_pos 1) e1
  have sig : 1 ≤ zz L i := by
    unfold zz
    linarith [Real.log_nonneg one]
  have early : zz L i ≤ H := by
    have h0 : 0 < Real.log (L.clock.hatBeta i) := by linarith
    calc _ = 1+Real.log (Real.log (L.clock.hatBeta i)) := rfl
         _ ≤ 1+Real.log (L.clock.hatBeta i) := by linarith [Real.log_le_self h0.le]
         _ ≤ L.clock.hatBeta i := by linarith [Real.log_le_sub_one_of_pos (WardBin.hot L i)]
         _ ≤ H := mono hib
  have H0 : 0 ≤ H := (WardBin.hot L b).le
  have sc : L.S.scale b ≤ c⁻¹*H := by
    rw [← div_eq_inv_mul,le_div_iff₀ hc]
    change _ ≤ L.clock.bar + G.slopeConstant*L.S.scale b
    dsimp [c]
    linarith [L.clock.bar_pos]
  have x0 : 0 ≤ L.S.scale i := by
    change 0 ≤ Real.log ((L.S.a i)⁻¹)
    apply Real.log_nonneg
    have hden : (1:ℝ) ≤ ((L.S.denominator i).val : ℝ) := by exact_mod_cast (L.S.denominator i).pos
    simpa [Schedule.a] using hden
  have rise := arc_span L.S i (b-i)
  rw [Nat.add_sub_of_le hib] at rise
  have gap : 0 ≤ L.S.scale b-L.S.scale i :=
    (mul_nonneg (Nat.cast_nonneg _) hh.le).trans rise
  have count : ((b-i : ℕ) : ℝ) ≤ h⁻¹*L.S.scale b := by
    rw [← div_eq_inv_mul,le_div_iff₀ hh]
    dsimp [h]
    linarith
  let z := zz L i + (L.S.scale b-L.S.scale i) + ((b-i : ℕ):ℝ)
  have z0 : 0 ≤ z := by dsimp [z]; positivity
  have zH : z ≤ B*H := by
    dsimp [z,B]
    have short := mul_le_mul_of_nonneg_left sc (show 0 ≤ h⁻¹ by positivity)
    linarith
  have bill : T.buy z ≤ (2+H)^(T.d+1) := by
    calc _ = T.x*z^T.d := rfl
         _ ≤ T.x*(B*H)^T.d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ z0 zH _) (zero_le_one.trans T.good)
         _ = (T.x*B^T.d)*H^T.d := by rw [mul_pow]; ring
         _ ≤ (2+H)^T.d*(2+H) := by
           rw [mul_comm (_^_) (2+H)]
           exact mul_le_mul (by linarith) (pow_le_pow_left₀ H0 (by linarith) _) (pow_nonneg H0 _) (by linarith)
         _ = (2+H)^(T.d+1) := (pow_succ ..).symm
  have g0 : 0 ≤ T.buy z := mul_nonneg (zero_le_one.trans T.good) (pow_nonneg z0 _)
  have h2 : 0 < 2+H := by linarith
  have growth : ((b-i:ℕ):ℝ)*(((T.d+1:ℕ):ℝ)*Real.log (2+H)) ≤
      ((((T.d+1:ℕ):ℝ)/h)*(1+L.S.scale b))*Real.log (2+H) := by
    have common : 0 ≤ (((T.d+1:ℕ):ℝ)*Real.log (2+H)) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    have nle : ((b-i:ℕ):ℝ) ≤ h⁻¹*(1+L.S.scale b) := by linarith [show 0 ≤ h⁻¹ by positivity]
    calc _ ≤ (h⁻¹*(1+L.S.scale b))*(((T.d+1:ℕ):ℝ)*Real.log (2+H)) :=
           mul_le_mul_of_nonneg_right nle common
         _ = _ := by rw [div_eq_mul_inv]; ring
  change (T.buy z)^(b-i) ≤ _
  calc _ ≤ ((2+H)^(T.d+1))^(b-i) := pow_le_pow_left₀ g0 bill _
       _ = Real.exp (((b-i:ℕ):ℝ)*(((T.d+1:ℕ):ℝ)*Real.log (2+H))) := by
         rw [Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log h2]
       _ ≤ _ := Real.exp_le_exp.mpr growth

variable {V : Type} [DecidableEq V] [Fintype V] (D k K : V→ℕ) (e : ℕ)

/-- The genuine finite Gears intake fee for carrying an already deposited row
from b down to i. The terminal mesh is fixed before all higher cutoffs. -/
theorem carried (L : Levels G) (simple : G.Simple) :
    let T := tollStep G D k K e Credit.leanC Credit.leanC
    ∀ᶠ i : ℕ in atTop, ∀ b ≥ i, ∀ Q : Realm G (e+1) Credit.leanC,
      Q.draws=L → Q.y=zz L → ∀ A : ℝ, 0≤A →
      fee (D:=D) (k:=k) Q K i b A ≤ WilsonMeasuredWindingSum.room L (((T.d+1:ℕ):ℝ)/Real.log 3) b * A := by
  intro T
  filter_upwards [band L simple T] with i h b hib Q hL hy A hA
  exact mul_le_mul_of_nonneg_right (by simpa [fee,horizon,T,hL,hy] using h b hib) hA

/-- Charge the full inherited fee to the original winding at its birth,
before summing over the ultraviolet history on a fixed physical period. -/
theorem invoice (R : Run G) (simple : G.Simple) (readout : RG05Preconstruction.ReadoutPurchase R.b) :
    let L := R.family.path.levels
    ∀ᶠ i : ℕ in atTop, ∀ (j per : ℕ) (Q : Realm G (e+1) Credit.leanC), Q.draws=L → Q.y=zz L →
      ∀ (s A : ℝ), 0<s → s⁻¹≤admittedCost L (i+j) → 0≤A →
      fee (D:=D) (k:=k) Q K i (i+j) A * Real.exp (-(s/512)*((R.family.side (i+j) per).val:ℝ)) ≤
      A * (Real.exp (-((L.S.period per).val:ℝ)*(L.clock.hatBeta i)^2/2048) * (1/2:ℝ)^j) := by
  intro L
  let T := tollStep G D k K e Credit.leanC Credit.leanC
  let c := (((T.d+1:ℕ):ℝ)/Real.log 3)
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  filter_upwards [carried D k K e L simple,WilsonMeasuredWindingSum.invoice R simple readout hc]
    with i carry sum j per Q hL hy s A hs paid hA
  calc _ ≤ (WilsonMeasuredWindingSum.room L c (i+j)*A) *
           Real.exp (-(s/512)*((R.family.side (i+j) per).val:ℝ)) :=
         mul_le_mul_of_nonneg_right (carry (i+j) (Nat.le_add_right ..) Q hL hy A hA) (Real.exp_pos _).le
       _ = A * (WilsonMeasuredWindingSum.room L c (i+j) * _) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (sum j per s hs paid) hA

end YM.Integration.WilsonInheritedWindingTransport
