import YM.Integration.WilsonSeparatedPrefixKineticMarket
import YM.Integration.WilsonMaxwellThermometerKineticCorridor
import YM.Integration.WilsonIndependentCollarClockRoom
import YM.Integration.WilsonReflectedOpticalWidth
import YM.Integration.WilsonReportingAbsoluteInletCoordinates

/-! Optical admission at the base is independent of both original cutoffs. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixKineticGeometry
open Function Filter Lattice Wilson RG RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Real
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Layout
open WilsonCoeffUV.Bank.Ticket
open WilsonSeparatedPrefixKineticMarket WilsonIndependentCollarClockRoom
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "V" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale
local notation "g" => regulatorRun R.family

def span (A b K:ℕ):Prop:=σ K-σ b ≤ A*log (H K)
def wage (b:ℕ):ℝ:=1+log (H b)

include simple in
theorem spend (C:ℝ)(d:ℕ):∀ᶠb:ℕ in atTop,∀N per,b ≤ N→C*(wage R b)^d ≤ (g N per b)⁻¹:=by
  have late: Tendsto (fun b=>log (H b)) atTop atTop:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate V simple)
  filter_upwards [late.eventually_ge_atTop (threshold C d)] with b money N per live
  have earned:=due C d (zero_lt_one.trans ((V).fits.delayed b)) money (R.makes.wilson.represents N per b live).band.1
  change C*(1+log (H b))^d≤((Real.sqrt (R.family.path.β N per b))⁻¹)⁻¹
  rw [inv_inv];exact earned

include simple in
theorem corridor (A:ℕ):∃B:ℝ,1 ≤ B ∧ ∀ᶠ b:ℕ in atTop,∀K N per,b ≤ K→K ≤ N→span R A b K→
    let Z:=wage R b
    (1 ≤ Z ∧ 1 ≤ aperture R b K ∧ aperture R b K ≤ B*Z ∧ ((K-b:ℕ):ℝ) ≤ B*Z) ∧
    ∀i,b ≤ i→i ≤ K→3/4 ≤ g N per i/g N per b ∧ g N per i/g N per b ≤ 5/4:=by
  let B:=3+(A:ℝ)+(A:ℝ)/log 2
  have l0:0<log 2:=log_pos (by norm_num)
  have a0:0 ≤ (A:ℝ)/log 2:=by positivity
  refine ⟨B,by dsimp [B];linarith [Nat.cast_nonneg (α:=ℝ) A],?_⟩
  let C:=8*(G.slopeConstant+1)*((A:ℝ)+1)
  have rise:Tendsto (fun b=>log (H b)) atTop atTop:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate V simple)
  filter_upwards [rise.eventually_ge_atTop (threshold C 1),WilsonReportingAbsoluteInletCoordinates.clocks R simple A] with b late times K N per bK KN short
  have h1:1 ≤ H b:=((V).fits.delayed b).le
  have h0:0<H b:=zero_lt_one.trans_le h1
  have k0:0<H K:=zero_lt_one.trans ((V).fits.delayed K)
  have Hk:H K ≤ 2*H b:=times bK short
  have z1:1 ≤ wage R b:=by unfold wage;linarith [log_nonneg h1]
  have logK:log (H K) ≤ wage R b:=by
    have bound:=Real.log_le_log k0 Hk
    rw [Real.log_mul (by norm_num: (2:ℝ)≠0) h0.ne'] at bound
    unfold wage;linarith only [bound,Real.log_le_sub_one_of_pos (by norm_num:0<(2:ℝ))]
  have gap:=short.trans (mul_le_mul_of_nonneg_left logK (Nat.cast_nonneg A))
  have dates:((K-b:ℕ):ℝ) ≤ ((A:ℝ)/log 2)*wage R b:=by
    rw [div_mul_eq_mul_div];apply (le_div_iff₀ l0).mpr
    exact (WilsonReflectedOpticalWidth.steps R bK).trans gap
  have wage0:0 ≤ wage R b:=by linarith
  have scaled:= (OPE.scale_mono R.family.S).monotone bK
  have pre:zz V b ≤ 2*wage R b:=by
    have up:=tiny_log V b
    unfold longLog at up;unfold wage;linarith only [up,log_nonneg h1]
  have low:1 ≤ zz V b:=by
    change 1 ≤ 1+log (log (H b));exact le_add_of_nonneg_right (Real.log_nonneg ((le_max_left ..).trans late))
  constructor
  · refine ⟨z1,?_,?_,?_⟩
    · unfold aperture;linarith [Nat.cast_nonneg (α:=ℝ) (K-b)]
    · unfold aperture B;linarith only [pre,gap,dates,wage0]
    · unfold B;linarith only [dates,wage0,mul_nonneg (Nat.cast_nonneg (α:=ℝ) A) wage0]
  · intro i bi iK
    have h:=WilsonMaxwellThermometerKineticCorridor.original R simple b i N per bi (iK.trans KN)
    have gi:log (R.family.S.a b)-log (R.family.S.a i)=σ i-σ b:=by simp [Schedule.scale];ring
    rw [gi] at h
    have bound:σ i-σ b ≤ (A:ℝ)*wage R b:=(sub_le_sub_right ((OPE.scale_mono R.family.S).monotone iK) _).trans gap
    have money:C*wage R b ≤ H b:=by
      have calc':=due C 1 h0 late (show H b/2 ≤ H b by linarith)
      rw [pow_one] at calc';refine calc'.trans ?_
      exact (Real.sqrt_le_iff).mpr ⟨h0.le,by nlinarith only [mul_nonneg h0.le (sub_nonneg.mpr h1)]⟩
    have width:2*(G.slopeConstant+1)*(σ i-σ b)/H b ≤ 1/4:=by
      apply (div_le_iff₀ h0).mpr;dsimp [C] at money
      have growth:0 ≤ G.slopeConstant+1:=by linarith [(Gauge.slopeConstant_pos simple).le]
      nlinarith only [money,mul_le_mul_of_nonneg_left bound (by positivity:0 ≤ 2*(G.slopeConstant+1)),mul_nonneg growth wage0]
    have hears:=abs_le.mp (h.trans width);constructor <;> linarith only [hears.1,hears.2]

end YM.Integration.WilsonSeparatedPrefixKineticGeometry
end
