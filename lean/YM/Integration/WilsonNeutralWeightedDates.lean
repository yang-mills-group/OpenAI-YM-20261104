import YM.FullVolume.Cross
import YM.Integration.WilsonMeasuredImpulseCalendar
import YM.RG01.Slack

/-! Chronological cost of comparing two neutral field transfers at the measured
Wilson couplings. The support of the sum is the original finite course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralWeightedDates
open Filter Finset Lattice Wilson RG Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators

variable {G : Gauge} (R : Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "gap" => regulatorRun R.family

private lemma inverse_step {x y : ℝ} (pos : 0 < x) (inc : x ≤ y) (near : y ≤ 2*x) (k : ℕ)
    (hk : 0 < k) : (y-x)/(x^(k+1)) ≤ 2*(1/x^k-1/y^k) := by
  have ypos := pos.trans_le inc
  have base : x/y ≤ 1 := (div_le_one ypos).mpr inc
  have p : (x/y)^k ≤ x/y := by
    simpa using (pow_le_pow_of_le_one (div_nonneg pos.le ypos.le) base hk : (x/y)^k ≤ (x/y)^1)
  rw [div_pow] at p
  have t : (y-x)/x ≤ 2*(1-x/y) := by
    have hy : 1-x/y = (y-x)/y := by field_simp
    rw [hy, ←mul_div_assoc, div_le_div_iff₀ pos ypos]
    nlinarith [mul_le_mul_of_nonneg_left near (sub_nonneg.mpr inc)]
  have t' : (y-x)/x ≤ 2*(1-x^k/y^k) := by linarith
  have paid := div_le_div_of_nonneg_right t' (pow_nonneg pos.le k)
  calc
    _ = (y-x)/x/x^k := by rw [pow_succ]; field_simp [pos.ne']
    _ ≤ _ := paid
    _ = _ := by field_simp [pos.ne',ypos.ne']

private theorem steps {m l : ℕ} (h : ∀ i, m ≤ i → H (i+1) ≤ 2*H i)
    (simple : G.Simple) (k : ℕ) (hk : 0<k) :
    ∑ s ∈ range l, (H (m+s+1)-H (m+s))/(H (m+s))^(k+1) ≤
      2*(1/(H m)^k-1/(H (m+l))^k) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ]; have pos : 0<H (m+l) := zero_lt_one.trans (R.family.path.levels.fits.delayed _)
    have mono := WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le
    have hi := inverse_step pos (mono (Nat.le_succ _)) (h _ (Nat.le_add_right m l)) k hk
    rw [show m + (l+1) = (m+l)+1 by omega]
    exact (add_le_add ih hi).trans_eq (by ring)

private theorem squared (N per i : ℕ) (live : i≤N) :
    (2*H i)⁻¹ ≤ gap N per i^2 ∧ gap N per i^2 ≤ 2/(H i) := by
  have band := (R.makes.wilson.represents N per i live).band
  have hpos : 0 < H i := zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  change H i/2 ≤ R.family.path.β N per i ∧ R.family.path.β N per i ≤ 2*H i at band
  have bp : 0 < R.family.path.β N per i := (half_pos hpos).trans_le band.1
  rw [regulatorRun, inv_pow, Real.sq_sqrt bp.le]
  constructor
  · exact inv_anti₀ bp band.2
  · rw [←one_div, div_le_div_iff₀ bp hpos]
    linarith only [band.1]

/-- An adjoint cost (H_i/H_m)^B consumes integrability at B, but the
reporting order loses just two coupling powers. The coarse date is chosen
before both regulators. -/
theorem original (simple : G.Simple) (B k : ℕ) (hk : 0<k) :
    ∀ᶠ m in atTop, ∀ N per, m≤N →
      ∑ s ∈ range (N-m), (H (m+s)/H m)^B * (gap N per (m+s))^(2*(B+k+1)) *
          Real.log (R.family.S.block (m+s)).val ≤
        (2:ℝ)^(2*(B+k)+2)/G.slopeConstant * (gap N per m)^(2*(B+k)) := by
  obtain ⟨m₀, ready⟩ := eventually_atTop.1 (RG01.Physical.nextHat simple R.family.path.levels)
  filter_upwards [eventually_ge_atTop m₀] with m late N per top
  have hp (i : ℕ) : 0<H i := zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have slope := Gauge.slopeConstant_pos simple
  let c : ℝ := 2^(B+k+1)/((H m)^B*G.slopeConstant)
  have hc : 0 ≤ c := div_nonneg (by positivity) (mul_nonneg (pow_nonneg (hp m).le B) slope.le)
  have item (s : ℕ) (hs : s∈range (N-m)) :
      (H (m+s)/H m)^B * gap N per (m+s)^(2*(B+k+1)) * Real.log (R.family.S.block (m+s)).val ≤
        c*((H (m+s+1)-H (m+s))/(H (m+s))^(k+1)) := by
    let i := m+s
    have il : i≤N := by have := mem_range.mp hs; dsimp [i]; omega
    have step : H (i+1)-H i = G.slopeConstant*Real.log (R.family.S.block i).val := by
      unfold Calendar.hatBeta
      rw [show R.family.path.levels.clock.schedule.scale (i+1)=
        R.family.S.scale i + Real.log (R.family.S.block i).val from R.family.S.scale_succ i]
      ring
    have lg : 0 ≤ Real.log (R.family.S.block i).val := Real.log_nonneg (by exact_mod_cast (R.family.S.block i).property)
    have pow := pow_le_pow_left₀ (sq_nonneg (gap N per i)) (squared R N per i il).2 (B+k+1)
    have priced := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left pow (pow_nonneg (div_nonneg (hp i).le (hp m).le) B)) lg
    change (H i/H m)^B * gap N per i^(2*(B+k+1)) * _ ≤ c*((H (i+1)-H i)/(H i)^(k+1))
    rw [pow_mul]
    apply priced.trans_eq
    rw [step]; dsimp [c]; rw [div_pow, div_pow, pow_add (H i) (B+k), pow_add (H i) B k, pow_one,
      pow_add (H i) k 1, pow_one]
    field_simp [(hp i).ne', (hp m).ne', slope.ne']
  have paid := sum_le_sum item
  rw [← mul_sum] at paid
  have bound := steps R (m:=m) (l:=N-m) (fun i mi => ready i (late.trans mi)) simple k hk
  have drop : 0 ≤ 1/(H (m+(N-m)))^k := div_nonneg zero_le_one (pow_nonneg (hp _).le k)
  have bs : ∑ s ∈ range (N-m), (H (m+s+1)-H (m+s))/(H (m+s))^(k+1) ≤ 2*(1/(H m)^k) := by linarith
  apply (paid.trans (mul_le_mul_of_nonneg_left bs hc)).trans
  have measured := pow_le_pow_left₀ (inv_nonneg.mpr (mul_nonneg (by norm_num) (hp m).le)) (squared R N per m top).1 (B+k)
  have coeff : 0 ≤ (2:ℝ)^(2*(B+k)+2)/G.slopeConstant := by positivity
  rw [pow_mul]
  apply (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left measured coeff)
  dsimp [c]
  rw [show 2*(B+k)+2=(B+k+1)+(B+k+1) by omega, pow_add (2:ℝ) (B+k+1),
    pow_succ (2:ℝ) (B+k), inv_pow, mul_pow, pow_add (H m) B k]
  field_simp [(hp m).ne', slope.ne']

end YM.Integration.WilsonNeutralWeightedDates
