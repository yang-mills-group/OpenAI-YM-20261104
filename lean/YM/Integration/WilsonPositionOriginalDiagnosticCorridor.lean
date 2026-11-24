import YM.Integration.WilsonPositionThermometerStationSubpower
import YM.Integration.WilsonMeasuredWindow

/-! The true extraction radius and the funded reporting date lie within
the station's original enlargement, uniformly before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticCorridor
open Function Set Filter Finset Lattice Wilson RG Source Climb Cells
open MergeProof.East Next.Rank Next.Rank.East Next.Rank.Station Next.Rank.Price
open WilsonMeasuredAdmission WilsonMeasuredWindow WilsonAdmissionScale
open scoped Topology BigOperators Classical
open private amount from YM.Integration.WilsonPositionThermometerStationSubpower
open private stop_min from YM.Integration.WilsonMeasuredWindow
variable {G:Gauge} (A:Levels G) (simple:G.Simple) (K:ℕ)

include simple in
theorem below : ∀ᶠ k in atTop, ∀ b:ℝ, 5<b →
    mast A k^K ≤ mag A b k := by
  let x:=WilsonAdmissionScale.logarithm A
  have grows:=WilsonAdmissionScale.logarithm_tendsto A simple
  filter_upwards [grows.eventually_ge_atTop 2,(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (2*K:ℝ)]
    with k full fee b large
  have x0:=WilsonAdmissionScale.logarithm_pos A k
  have term:mast A k≤x k^2:=by change 2+WilsonAdmissionScale.logarithm A k≤WilsonAdmissionScale.logarithm A k^2; nlinarith
  have expo: ((x k)^2)^K=Real.exp (2*(K:ℝ)*Real.log (x k)):=by
    rw [←pow_mul];rw [show 2*(K:ℝ)=((2*K:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log x0]
  have held : Real.exp (2*(K:ℝ)*Real.log (x k)) ≤ A.clock.monitor k:=by
    apply Real.exp_le_exp.mpr
    change 2*(K:ℝ)*Real.log (x k) ≤ (Real.log (x k))^2
    change 2*(K:ℝ)≤Real.log (x k) at fee
    exact (mul_le_mul_of_nonneg_right fee (Real.log_nonneg (by dsimp only [x]; linarith))).trans_eq (by ring)
  have p:1≤A.clock.monitor k:=Real.one_le_exp (sq_nonneg _)
  have high: A.clock.monitor k ≤ mag A b k:=by
    unfold mag
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le p (show (1:ℝ)≤b by linarith)
  exact (pow_le_pow_left₀ (mast_pos A k).le term _).trans (expo.le.trans (held.trans high))

include simple in
theorem upper {e:ℝ} (positive:0<e) : ∀ᶠ k in atTop, ∀ b:ℝ, b≤Perch.y (A.clock.hatBeta k) →
    mag A b k ≤ (A.clock.hatBeta k)^e := by
  filter_upwards [(hat_rate A simple).eventually (amount 1 0 e positive)] with k credit b h
  have paid:=credit b h
  simp only [pow_zero,pow_one,mul_one] at paid
  rw [Atlas.mag_bill]
  change Real.exp ((Perch.y (A.clock.hatBeta k))^2*b)≤_
  linarith only [paid,Real.exp_pos ((Perch.y (A.clock.hatBeta k))^2*b)]

/-- The radius chosen on this star meets the actual reporting rule. The true
number of blocks between the dates need not be bounded. -/
theorem original {e:ℝ} (positive:0<e) : ∀ᶠ k in atTop, ∀ b:ℝ,5<b → b≤Perch.y (A.clock.hatBeta k) →
    let r:=gap A b k
    let m:=WilsonMeasuredWindow.stop A simple K r
    m≤k ∧ A.S.a m / A.S.a k ≤ (A.clock.hatBeta k)^e ∧ A.clock.hatBeta k ≤ 2*A.clock.hatBeta m := by
  have sub := Real.isLittleO_log_id_atTop.bound (c:=(2*G.slopeConstant)⁻¹) (by positivity [Gauge.slopeConstant_pos simple])
  filter_upwards [below A simple K,upper A simple positive,upper A simple (show 0<(1:ℝ) by norm_num),
      (hat_rate A simple).eventually sub] with k low cheap one small b large high
  let r:=gap A b k
  let m:=WilsonMeasuredWindow.stop A simple K r
  have rad:0<r:=gap_pos A b k
  have mk:m≤k:=by
    by_contra! anti
    have strict:=stop_min A simple K rad anti
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (low b large) (A.S.a_pos k).le)) strict
  have a:A.S.a m≤r:=
    (le_mul_of_one_le_right (A.S.a_pos m).le (one_le_pow₀ (mast_gt_one A m).le)).trans
      (stop_spec (K:=K) (A:=A) (hG:=simple) rad)
  have ratio:A.S.a m / A.S.a k ≤ mag A b k:=(div_le_iff₀ (A.S.a_pos k)).mpr (by simpa only [r,gap,mul_comm] using a)
  have cap:A.S.a m / A.S.a k ≤ A.clock.hatBeta k:=by simpa only [Real.rpow_one] using ratio.trans (one b high)
  have δ:G.slopeConstant*(A.S.scale k-A.S.scale m) ≤ G.slopeConstant*Real.log (A.clock.hatBeta k):=by
    have x:=Real.log_le_log (div_pos (A.S.a_pos m) (A.S.a_pos k)) cap
    rw [Real.log_div (A.S.a_pos m).ne' (A.S.a_pos k).ne',Stock.a_log A.S m,Stock.a_log A.S k,Real.log_exp,Real.log_exp] at x
    exact mul_le_mul_of_nonneg_left (by linarith) (Gauge.slopeConstant_pos simple).le
  have price:G.slopeConstant*Real.log (A.clock.hatBeta k) ≤ A.clock.hatBeta k/2 := by
    have cost:= (le_abs_self (Real.log (A.clock.hatBeta k))).trans small
    simp only [id_eq] at cost
    rw [Real.norm_of_nonneg (zero_le_one.trans (A.fits.delayed k).le)] at cost
    have s:=Gauge.slopeConstant_pos simple
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
    calc
      _ = (2*G.slopeConstant)*Real.log (A.clock.hatBeta k) := by ring
      _ ≤ (2*G.slopeConstant)*((2*G.slopeConstant)⁻¹*A.clock.hatBeta k) := mul_le_mul_of_nonneg_left cost (by positivity)
      _ = _ := by field_simp
  have value:A.clock.hatBeta k-A.clock.hatBeta m=G.slopeConstant*(A.S.scale k-A.S.scale m):=by
    unfold Calendar.hatBeta Levels.S;ring
  exact ⟨mk,ratio.trans (cheap b high),by linarith only [value,δ,price]⟩

end YM.Integration.WilsonPositionOriginalDiagnosticCorridor
