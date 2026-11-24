import YM.Integration.WilsonAxialReach

/-! The cost of the complete original periodic aperture is subpower, and its exceptional set is all-order flat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAxialRates

open Function Filter RG OPE.Therm WilsonAxialReach
open scoped Topology
variable {G : Gauge}

theorem controlled (A : Levels G) (hG : G.Simple) (d h j k : ℕ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun m => (1+(reach A d h m:ℝ))^j*(sigmaU A m)^k/(A.clock.hatBeta m)^s)
      atTop (𝓝 0) := by
  let p := (2*h)*j+k
  let K : ℝ := (1+(d:ℝ)*3^h)^j
  have source := (isLittleO_log_rpow_rpow_atTop (p:ℝ) hs).tendsto_div_nhds_zero.comp (Next.Rank.Station.hat_rate A hG)
  have hlim := source.const_mul K
  rw [mul_zero] at hlim
  have hnn (m : ℕ) : 0≤(1+(reach A d h m:ℝ))^j*(sigmaU A m)^k/(A.clock.hatBeta m)^s := by
    have hx : 0<A.clock.hatBeta m := zero_lt_one.trans (A.fits.delayed m)
    have hL : 0 ≤ sigmaU A m := (Real.log_pos (A.fits.delayed m)).le
    positivity
  refine squeeze_zero' (Eventually.of_forall hnn) ?_ hlim
  filter_upwards [(log_raised (K:=A) hG).eventually_ge_atTop 1] with m hm
  let x := A.clock.hatBeta m
  let L := Real.log x
  let B := (A.budget m).B
  have hL : 1≤L := hm
  have hx : 0<x := zero_lt_one.trans (A.fits.delayed m)
  have hb : 1+(B:ℝ)≤3*L^2 := by
    change 1+(⌈L^2⌉₊:ℝ)≤_
    linarith [Nat.ceil_lt_add_one (sq_nonneg L),one_le_pow₀ (n:=2) hL]
  have hp := pow_le_pow_left₀ (by positivity) hb h
  rw [mul_pow,←pow_mul] at hp
  have hr : (reach A d h m:ℝ)≤(d:ℝ)*3^h*L^(2*h) := by
    calc
      _ = (d:ℝ)*(1+(B:ℝ))^h := by simp [reach,B,add_comm]
      _ ≤ (d:ℝ)*(3^h*L^(2*h)) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg d)
      _ = _ := by ring
  have hR : 1+(reach A d h m:ℝ)≤(1+(d:ℝ)*3^h)*L^(2*h) := by
    rw [add_mul,one_mul]
    exact add_le_add (one_le_pow₀ hL) hr
  have hj := pow_le_pow_left₀ (by positivity) hR j
  rw [mul_pow,←pow_mul] at hj
  change (1+(reach A d h m:ℝ))^j*L^k/x^s ≤ K*(L^(p:ℝ)/x^s)
  rw [Real.rpow_natCast]
  calc
    _ ≤ (K*L^((2*h)*j))*L^k/x^s := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hj (pow_nonneg (zero_le_one.trans hL) _)) (Real.rpow_nonneg hx.le _)
    _ = _ := by dsimp only [p];rw [pow_add];ring

theorem erased (H : History G) (hG : G.Simple) (d h j k q : ℕ) :
    Tendsto (fun m => (1+(reach H.levels d h m:ℝ))^j*(sigmaU H.levels m)^k*
      (H.levels.clock.hatBeta m)^q*vanishP H.levels m) atTop (𝓝 0) := by
  let A := H.levels
  have hnn (m : ℕ) : 0≤(1+(reach A d h m:ℝ))^j*(sigmaU A m)^k*(A.clock.hatBeta m)^q*vanishP A m := by
    have hx : 0<A.clock.hatBeta m := zero_lt_one.trans (A.fits.delayed m)
    have hL : 0 ≤ sigmaU A m := (Real.log_pos (A.fits.delayed m)).le
    have he : 0<vanishP A m := Real.exp_pos _
    positivity
  refine squeeze_zero' (Eventually.of_forall hnn) ?_ (disappears (H:=H) hG (q+1))
  filter_upwards [(controlled A hG d h j k zero_lt_one).eventually (gt_mem_nhds zero_lt_one)] with m hm
  let x := A.clock.hatBeta m
  have hx : 0<x := zero_lt_one.trans (A.fits.delayed m)
  have ha : (1+(reach A d h m:ℝ))^j*(sigmaU A m)^k/x<1 := by simpa only [Real.rpow_one] using hm
  have hp := ((div_lt_iff₀ hx).mp ha).le
  rw [one_mul] at hp
  calc
    _ ≤ x*x^q*vanishP A m := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (pow_nonneg hx.le _)) (Real.exp_pos _).le
    _ = _ := by change x*x^q*vanishP A m=x^(q+1)*vanishP A m;rw [pow_succ];ring

end YM.Integration.WilsonAxialRates
end
