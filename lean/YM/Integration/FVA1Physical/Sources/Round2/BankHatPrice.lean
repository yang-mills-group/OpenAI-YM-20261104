import YM.Integration.FVA1Physical.Sources.Round2.ClockAtHat
import YM.Integration.FVA1Physical.Wilson.IteratedBankGate

/-! The full rooted norm of a distributed coefficient bank at the origin pays
the size of its reading throughout the selected logarithmic chart. This
estimate is independent of the number of sites in the period. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open Push.Uniform MSbar.Rolling MSbar MSbar.Mosaic MSbar.Whisk MSbar.Bout MSbar.Bakery MSbar.Bakery.Portal MSbar.Cacao MSbar.Lis
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem bank_hat_price (p m:ℕ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ y:ℝ in atTop,∀ {f:Side} (b:Site f) (s:ℕ) (δ g:ℝ) (T:Nesting G f),
      BankPaid b y s p m δ T → |g| ≤ 1 → ∀ Z:Positions (Primary f G),‖Z‖ ≤ hatW y/32 →
      |clockReading p g T Z| ≤ y^(δ+ε) := by
  let rise:Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  have fees:=Run.Ypow rise (Run.stanza rise) (m+1)
  filter_upwards [fees (ε/2) (half_pos hε),(tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop (p+1:ℕ),
    Alto.broad.eventually_ge_atTop 2,eventually_gt_atTop (0:ℝ)] with y slow many high pos
  intro f b s δ g T bank small Z room
  have ha:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have width:(1+hatW y/32)^(m+1) ≤ y^(ε/2):=by
    apply (pow_le_pow_left₀ (by linarith only [high]) (show 1+hatW y/32 ≤ hatW y by linarith only [high]) _).trans
    exact (le_abs_self _).trans slow
  have row (i:ℕ) (hi:i ≤ p):|g^i*MvPolynomial.eval Z (PowerSeries.coeff i T)| ≤ y^δ*y^(ε/2):=by
    have h:=(bank i hi)
    have pay:=Bout.looks ha (Bout.across Z h.2 ha (by simpa only [sub_zero] using room) h.1 0)
    rw [abs_mul,abs_pow]
    exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) small)).trans
      (pay.trans (mul_le_mul_of_nonneg_left width (Real.rpow_nonneg pos.le _)))
  unfold clockReading taste picture
  simp only [PowerSeries.coeff_map]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (fun i hi=>row i (Nat.lt_succ_iff.mp (mem_range.mp hi)))).trans
  rw [sum_const,card_range,nsmul_eq_mul]
  calc (p+1:ℕ)*(y^δ*y^(ε/2)) ≤ y^(ε/2)*(y^δ*y^(ε/2)) := mul_le_mul_of_nonneg_right many (by positivity)
       _=y^(δ+ε):=by rw [←mul_assoc,←Real.rpow_add pos,←Real.rpow_add pos]; congr 1;ring

end YM.Integration.FVA1Physical.Round2.Curvature
