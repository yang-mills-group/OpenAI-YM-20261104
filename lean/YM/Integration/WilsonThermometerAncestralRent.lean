import YM.Integration.WilsonLocalCompactRichPortUnits
import YM.Integration.WilsonThermometerAncestralTrace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralRent
open Finset Filter Real Lattice Wilson RG RG16 Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open scoped BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "increment" => G.slopeConstant*Real.log (3:ℝ)

include simple in
private theorem grows (j:ℕ):increment ≤ H (j+1)-H j:=by
  have lower:(3:ℝ) ≤ ((A).S.block j).val:=by exact_mod_cast (A).S.block_large j
  have step:=mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) lower) (G.slopeConstant_pos simple).le
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]
  linarith

private theorem telescopes (h:ℕ → ℝ) {i t:ℕ} (step:i ≤ t) :
    (∑j∈Ico i t,(h j-h (j+1)))=h i-h t:=by
  induction t, step using Nat.le_induction with
  | base => simp
  | succ j hj ih => rw [sum_Ico_succ_top hj,ih];ring

include simple in
/-- One full power-sum on the actual measured Wilson temperatures, with a two-power loss. -/
theorem original {i t N:ℕ} (it:i ≤ t) (top:t<N) (per p:ℕ) :
    let g:=regulatorRun R.family N per
    ∑j∈Ico i t,(g (j+2))^(p+4) ≤ ((8:ℝ)*2^p/(increment))*(g i)^(p+2) :=by
  intro g
  have hp(j):0<H j:=zero_lt_one.trans ((A).fits.delayed j)
  have b:0 < (increment):=mul_pos (G.slopeConstant_pos simple) (Real.log_pos (by norm_num))
  have mono:=WilsonStartup.Timing.hat_mono (A) (G.slopeConstant_pos simple).le
  have gp(j):0 ≤ g j:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have banded (j:ℕ) (cut:j ≤ N):g j^2 ≤ 2/(H j) ∧ (H j)⁻¹ ≤ 2*(g j)^2:=by
    let β:=R.family.path.β N per j
    have data: H j/2 ≤ β ∧ β ≤ 2*H j:=(R.makes.wilson.represents N per j cut).band
    have pos:0<β:=(half_pos (hp j)).trans_le data.1
    have square:g j^2=β⁻¹:=by
      change (Real.sqrt β)⁻¹^2=β⁻¹
      rw [inv_pow,Real.sq_sqrt pos.le]
    rw [square]
    constructor
    · calc
        β⁻¹ ≤ (H j/2)⁻¹:=inv_anti₀ (half_pos (hp j)) data.1
        _ = _:=by field_simp [(hp j).ne']
    · calc
        (H j)⁻¹ ≤ (β/2)⁻¹:=inv_anti₀ (half_pos pos) (by linarith only [data.2])
        _ = _:=by field_simp [pos.ne']
  have price (j:ℕ):increment/(H (j+1))^2 ≤ (H j)⁻¹-(H (j+1))⁻¹:=by
    calc
      _ ≤ increment/(H j*H (j+1)):=div_le_div_of_nonneg_left b.le (mul_pos (hp _) (hp _))
        (by simpa [pow_two] using mul_le_mul_of_nonneg_right (mono (Nat.le_succ j)) (hp (j+1)).le)
      _ ≤ (H (j+1)-H j)/(H j*H (j+1)):=div_le_div_of_nonneg_right (grows R simple j) (mul_nonneg (hp _).le (hp _).le)
      _ = _:=by field_simp [(hp j).ne',(hp (j+1)).ne']
  let K:ℝ:=(2*g i)^p*(4/(increment))
  have K0:0 ≤ K:=mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (gp _)) _) (div_nonneg (by norm_num) b.le)
  have one(j:ℕ)(belongs:j∈Ico i t):
      (g (j+2))^(p+4) ≤ K*((H (j+1))⁻¹-(H (j+2))⁻¹):=by
    obtain ⟨ij,jt⟩:=mem_Ico.mp belongs
    have fin:j+2 ≤ N:=by omega
    have relative:=WilsonLocalCompactRichPortUnits.compared R simple (show i ≤ j+2 by omega) fin per
    calc
      _ = (g (j+2))^p*((g (j+2))^2)^2:=by rw [pow_add];ring
      _ ≤ (2*g i)^p*(2/(H (j+2)))^2:=mul_le_mul
        (pow_le_pow_left₀ (gp _) relative _) (pow_le_pow_left₀ (sq_nonneg _) (banded _ fin).1 _)
        (sq_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) (gp _)) _)
      _ = K*((increment)/(H (j+2))^2):=by dsimp only [K];field_simp [b.ne',(G.slopeConstant_pos simple).ne',(hp (j+2)).ne'];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (price (j+1)) K0
  have tel:(∑j∈Ico i t,((H (j+1))⁻¹-(H (j+2))⁻¹))=(H (i+1))⁻¹-(H (t+1))⁻¹:=by
    exact telescopes (fun j:ℕ=> (H (j+1))⁻¹) it
  have entry:(H (i+1))⁻¹ ≤ 2*g i^2:=(inv_anti₀ (hp i) (mono (Nat.le_succ i))).trans (banded i (it.trans top.le)).2
  calc
    _ ≤ ∑j∈Ico i t,K*((H (j+1))⁻¹-(H (j+2))⁻¹):=sum_le_sum one
    _ = K*((H (i+1))⁻¹-(H (t+1))⁻¹):=by rw [←mul_sum,tel]
    _ ≤ K*(2*g i^2):=mul_le_mul_of_nonneg_left (le_trans (sub_le_self _ (inv_nonneg.mpr (hp _).le)) entry) K0
    _ = _:=by dsimp only [K];rw [mul_pow,pow_add];ring

end YM.Integration.WilsonThermometerAncestralRent
