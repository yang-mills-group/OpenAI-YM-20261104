import YM.Integration.WilsonFirstReceivedRadialComparison
import YM.RG01.Slack
import YM.Integration.ActualCoarseStagePrice
import YM.Next.RANK.NoSpill

/-! On the original reporting clock, the fixed radial interpolation cost
on the local axial plaquette room takes at most one spare running-coupling
power, uniformly over all finer cutoffs and periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedRadialRoom
open Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato
open Pert.Asymptotics Next.Rank.Perch
open WilsonFirstReceivedRadialStencil
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem tariff (C A:ℝ) (cc:0 ≤ C) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ x:ℝ in atTop,C*bill A x*(Real.sqrt x)⁻¹ ≤ ε := by
  have drops: Tendsto (fun x=>C*bill (-1) x) atTop (𝓝 0) := by
    simpa using (bill_hi (by norm_num : (-1:ℝ)<0)).const_mul C
  filter_upwards [Next.Rank.Paint.cooling (-(A+1)),drops.eventually (ge_mem_nhds ep)] with x h e
  have frost : (Real.sqrt x)⁻¹ ≤ bill (-(A+1)) x := by
    change |(Real.sqrt x)⁻¹| ≤ _ at h
    rwa [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] at h
  calc
    _ ≤ C*bill A x*bill (-(A+1)) x := mul_le_mul_of_nonneg_left frost (mul_nonneg cc (Real.exp_pos _).le)
    _ = C*bill (-1) x := by rw [mul_assoc,overlap]; congr 2; ring
    _ ≤ _ := e

theorem original (R:Run G) (simple:G.Simple) (D k:ℕ) (H:ℝ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N per:ℕ,m+1 ≤ N→
      let x := R.family.path.levels.clock.hatBeta m
      let g := regulatorRun R.family N per (m+1)
      let B := R.family.path.levels.budget m
      let t := (B.B:ℝ)^2*B.threshold
      ∀ z:ℝ,(abs z) ≤ (abs H)*(Real.log x)^k*t/g →
        budget D*(1+(abs z))^D*g ≤ ε := by
  let V := R.family.path.levels
  let c := 2*budget D*(1+8*(abs H))^D
  have bp:0 ≤ budget D := by unfold budget; positivity
  have cp:0 ≤ c := by dsimp [c]; positivity
  have grows := RG01.Physical.hats simple V
  filter_upwards [RG01.Physical.nextHat simple V,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp grows)).eventually_ge_atTop 1,
    grows.eventually_ge_atTop 4,grows (tariff c (((k+5)*D:ℕ):ℝ) cp ep)] with m near loglog large paid
  intro N per hm x g B t z hz
  let s := Real.log x
  let M := Real.exp ((Real.log s)^2)
  let beta := R.family.path.β N per (m+1)
  have xp:0<x := by change 4 ≤ x at large; linarith
  have sp:0<s := Real.log_pos (by change 4 ≤ x at large; linarith)
  have logs:1 ≤ Real.log s := loglog
  have one:1 ≤ s := by
    by_contra! bad
    exact (Real.log_neg sp bad).not_ge (zero_le_one.trans logs)
  have mon:1 ≤ M := Real.one_le_exp (sq_nonneg _)
  have logpay:s ≤ M := by
    calc
      s=Real.exp (Real.log s) := (Real.exp_log sp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [logs,sq_nonneg (Real.log s-1)])
  have clocks:x ≤ V.clock.hatBeta (m+1) := ActualCoarseStagePrice.hatBeta_mono V simple (Nat.le_succ m)
  have band := (R.makes.wilson.represents N per (m+1) hm).band
  change V.clock.hatBeta (m+1)/2 ≤ beta ∧ beta ≤ 2*V.clock.hatBeta (m+1) at band
  have betapos:0<beta := by linarith only [xp,clocks,band.1]
  have upper:Real.sqrt beta ≤ 2*Real.sqrt x := by
    calc
      _ ≤ Real.sqrt (4*x) := Real.sqrt_le_sqrt (by linarith only [band.2,near])
      _=_ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have lower:Real.sqrt x ≤ 2*Real.sqrt beta := by
    calc
      _ ≤ Real.sqrt (4*beta) := Real.sqrt_le_sqrt (by linarith only [clocks,band.1,betapos])
      _=_ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have Gpos:0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have small:g ≤ 2*(Real.sqrt x)⁻¹ := by
    change (Real.sqrt beta)⁻¹ ≤ _
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr betapos) (Real.sqrt_pos.mpr xp)]
    simpa using lower
  have ceilBound:(B.B:ℝ) ≤ 2*s^2 := by
    have hc:(B.B:ℝ) ≤ s^2+1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
    linarith only [hc,one_le_pow₀ one (n := 2)]
  have walk:(B.B:ℝ)^2 ≤ 4*s^4 := (pow_le_pow_left₀ (Nat.cast_nonneg _) ceilBound 2).trans_eq (by ring)
  have room:t/g ≤ 8*s^4*M := by
    change (B.B:ℝ)^2*((Real.sqrt x)⁻¹*M)/(Real.sqrt beta)⁻¹ ≤ _
    rw [div_inv_eq_mul]
    calc
      _ ≤ (4*s^4)*((Real.sqrt x)⁻¹*M)*(2*Real.sqrt x) := mul_le_mul
        (mul_le_mul_of_nonneg_right walk (by positivity)) upper (Real.sqrt_nonneg _) (by positivity)
      _=_ := by field_simp [(Real.sqrt_pos.mpr xp).ne']; ring
  have size:(abs z) ≤ 8*(abs H)*(s^(k+4)*M) := by
    calc
      _ ≤ (abs H)*s^k*(t/g) := hz.trans_eq (by ring)
      _ ≤ (abs H)*s^k*(8*s^4*M) := mul_le_mul_of_nonneg_left room (by positivity)
      _=_ := by rw [pow_add];ring
  have unit:1 ≤ M^(k+5) := one_le_pow₀ mon
  have y:s^(k+4)*M ≤ M^(k+5) := by
    calc
      _ ≤ M^(k+4)*M := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ sp.le logpay _) (zero_le_one.trans mon)
      _ = M^(k+5) := (pow_succ M (k+4)).symm
  have cap:1+(abs z) ≤ (1+8*(abs H))*M^(k+5) := by
    rw [add_mul,one_mul]
    exact add_le_add unit (size.trans (mul_le_mul_of_nonneg_left y (by positivity)))
  have expfee:M^((k+5)*D)=bill (((k+5)*D:ℕ):ℝ) x := by
    dsimp [M,bill,boil,Next.Rank.Perch.y,s]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ budget D*((1+8*(abs H))*M^(k+5))^D*(2*(Real.sqrt x)⁻¹) := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) cap _) bp) small Gpos (by positivity)
    _=c*bill (((k+5)*D:ℕ):ℝ) x*(Real.sqrt x)⁻¹ := by
      rw [mul_pow,←pow_mul,expfee]; dsimp [c]; ring
    _ ≤ _ := paid

end YM.Integration.WilsonFirstReceivedRadialRoom
