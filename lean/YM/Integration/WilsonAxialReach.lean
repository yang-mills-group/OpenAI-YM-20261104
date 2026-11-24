import YM.OPE.Therm.Rite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Polynomial local windows fit in every actual period and lie inside each fixed small-field chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAxialReach

open Filter Lattice Wilson RG OPE.Therm
open scoped Topology

variable {G : Gauge}

def reach (A : Levels G) (d h m : ℕ) := d*((A.budget m).B+1)^h

theorem denominator (S : Schedule) (m p : ℕ) : (S.denominator m).val ≤ (S.side m p).val :=
  Nat.le_mul_of_pos_left (S.denominator m).val (S.period p).property

theorem fixed (S : Schedule) (r : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ p, 2*r < (S.side m p).val := by
  filter_upwards [S.den_strict.tendsto_atTop.eventually_gt_atTop (2*r)] with m hm p
  exact hm.trans_le (denominator S m p)

theorem embedded (A : Levels G) (hG : G.Simple) (d h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ p, 2*reach A d h m < (A.S.side m p).val := by
  let M := (2:ℝ)*d*3^h
  have ht := (ember_mul (K:=A) hG (2*h)).const_mul M
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with m hm p
  let x := A.clock.hatBeta m
  let B := (A.budget m).B
  have hx : 1 < x := A.fits.delayed m
  have hh : 1+(B:ℝ) ≤ 3*x^2 := by
    change 1+(⌈(Real.log x)^2⌉₊:ℝ) ≤ _
    have hlog := Real.log_pos hx
    nlinarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hx),
      Nat.ceil_lt_add_one (sq_nonneg (Real.log x)),sq_nonneg (x-1)]
  have hp := pow_le_pow_left₀ (by positivity) hh h
  rw [mul_pow,←pow_mul] at hp
  have hsmall : A.S.a m*(2*(d:ℝ)*(1+(B:ℝ))^h) < 1 := by
    calc
      _ ≤ A.S.a m*(2*(d:ℝ)*(3^h*x^(2*h))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) (A.S.a_pos _).le
      _ = M*(A.S.a m*x^(2*h)) := by dsimp only [M];ring
      _ < _ := hm
  let a := ((A.S.denominator m).val:ℝ)
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast (A.S.denominator m).property
  have hdiv : 2*(d:ℝ)*(1+(B:ℝ))^h/a < 1 := by
    simpa only [Schedule.a,a, div_eq_mul_inv,mul_comm] using hsmall
  have hn := (div_lt_one ha).mp hdiv
  have hnat : 2*reach A d h m < (A.S.denominator m).val := by
    unfold reach
    have hreal : 2*((d:ℝ)*((B:ℝ)+1)^h) < a := by rw [←mul_assoc,add_comm (B:ℝ)]; exact hn
    dsimp only [a,B] at hreal
    exact_mod_cast hreal
  exact hnat.trans_le (denominator A.S m p)

theorem cools (A : Levels G) (hG : G.Simple) (d h : ℕ) :
    Tendsto (fun m => (reach A d h m:ℝ)*cool A m) atTop (𝓝 0) := by
  let p := 2*h+12
  let M := (d:ℝ)*3^h
  have hl := (isLittleO_log_rpow_rpow_atTop (p:ℝ) (show 0 < (1/2:ℝ) by norm_num)).tendsto_div_nhds_zero
  have hh := hl.comp (Next.Rank.Station.hat_rate A hG)
  have hh' := hh.const_mul M
  rw [mul_zero] at hh'
  have hnon (m : ℕ) : 0≤(reach A d h m:ℝ)*cool A m := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by positivity)
  refine squeeze_zero' (Eventually.of_forall hnon) ?_ hh'
  filter_upwards [(log_raised (K:=A) hG).eventually_ge_atTop 1] with m hm
  let x := A.clock.hatBeta m
  let B := (A.budget m).B
  let L := Real.log x
  have hL : 1 ≤ L := hm
  have hb : 1+(B:ℝ) ≤ 3*L^2 := by
    change 1+(⌈L^2⌉₊:ℝ) ≤ _
    linarith [Nat.ceil_lt_add_one (sq_nonneg L),one_le_pow₀ (n:=2) hL]
  have hp := pow_le_pow_left₀ (by positivity) hb h
  rw [mul_pow,←pow_mul] at hp
  have hg : 0 ≤ (Real.sqrt x)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  change (reach A d h m:ℝ)*((Real.sqrt x)⁻¹*L^12) ≤ M*(L^(p:ℝ)/x^(1/2:ℝ))
  rw [Real.rpow_natCast,←Real.sqrt_eq_rpow]
  calc
    _ = (d:ℝ)*(1+(B:ℝ))^h*((Real.sqrt x)⁻¹*L^12) := by simp [reach,B,add_comm]
    _ ≤ (d:ℝ)*(3^h*L^(2*h))*((Real.sqrt x)⁻¹*L^12) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
        (mul_nonneg hg (pow_nonneg (zero_le_one.trans hL) _))
    _ = _ := by dsimp only [p,M]; rw [pow_add,div_eq_mul_inv]; ring

end YM.Integration.WilsonAxialReach
end
