import YM.Integration.WilsonMeasuredPointTopCoin
import YM.Integration.WilsonOlderFreshPointEarnedEdge
import YM.Next.WARD_BIN.Coin

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointDatedCoin
open Lattice RG Wilson Labels Next.Foundations
open PhysicalNext.Repeat.Legato WilsonNeutralCopiedField WilsonNeutralCopiedProgram WilsonNeutralCutoffAlphabet
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G) {d:ℕ} (i N per:ℕ)
local notation "C" => R.family
local notation "F" => R.family.labels.level d
local notation "B" => R.family.path.levels.clock
local notation "g₀" => ConnectedActivityE6.Coat.gStep (R.family.path.rep N per i).beta
local notation "t₀" => (B).threshold i
theorem ratio (live:i≤N) : 0 < g₀*t₀⁻¹ ∧ (g₀*t₀⁻¹)^2≤2 := by
  let H:ℝ:=(B).hatBeta i
  let β:=(R.family.path.rep N per i).beta
  let m:ℝ:=(B).monitor i
  have hp:0<H:=zero_lt_one.trans (R.alloy.B.a.fits.delayed i)
  have bp:0<β:=Overlay.beta_positive R.makes.wilson (m:=i) (N:=N) (p:=per) live
  have band:H/2≤β:=(R.makes.wilson.represents N per i live).band.1
  have paid:1≤ m:=Real.one_le_exp (sq_nonneg _)
  have ht:t₀=(Real.sqrt H)⁻¹*m:=rfl
  have tp:0<t₀:=ht.symm ▸ mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hp)) (zero_lt_one.trans_le paid)
  have gp:0<g₀:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  refine ⟨mul_pos gp (inv_pos.mpr tp),?_⟩
  have ts:H⁻¹≤ t₀^2:=by
    rw [ht,mul_pow,inv_pow,Real.sq_sqrt hp.le]
    exact le_mul_of_one_le_right (inv_nonneg.mpr hp.le) (one_le_pow₀ paid)
  have gs:g₀^2=β⁻¹:=by change ((Real.sqrt β)⁻¹)^2=β⁻¹;rw [inv_pow,Real.sq_sqrt bp.le]
  have gain:β⁻¹≤2*H⁻¹:=by rw [←div_eq_mul_inv,le_div_iff₀ hp,inv_mul_eq_div,div_le_iff₀ bp];linarith only [band]
  rw [←div_eq_mul_inv,div_pow,div_le_iff₀ (pow_pos tp _),gs]
  exact gain.trans (mul_le_mul_of_nonneg_left ts (by norm_num))


/-- The signed coefficients of the dated, compensated primary. -/
def coin (x:R.family.label d)(phase:ℂ→ₗ[ℝ]ℝ)(b:(F).Index):ℝ:=
  phase (((F).scaled t₀⁻¹ (Next.Rank.Price.awake (C) d i N per x)) b) *g₀^((F).grades b).2

theorem printed (x:R.family.label d)(phase:ℂ→ₗ[ℝ]ℝ)(b:(F).Index):
    coin R i N per x phase b=(g₀*t₀⁻¹)^((F).grades b).2*phase ((Next.Rank.Price.awake (C) d i N per x) b):=by
  rw [coin,Labels.Frame.scaled_apply,←Complex.real_smul,map_smul,smul_eq_mul,mul_pow]
  ring

theorem wage (live:i≤N)(x:R.family.label d)(phase:ℂ→ₗ[ℝ]ℝ):
    (∑b:(F).Index,|coin R i N per x phase b|)≤(2:ℝ)^d*‖phase.toContinuousLinearMap‖*
      Next.Rank.Spindle.paid (C) d i N per x:=by
  obtain ⟨pos,cap⟩:=ratio R i N per live
  have gain:g₀*t₀⁻¹≤2:=by nlinarith only [cap,sq_nonneg (g₀*t₀⁻¹-1)]
  let X:=Next.Rank.Price.awake (C) d i N per x
  unfold Next.Rank.Spindle.paid Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _=>?_
  have rank:((F).grades b).2≤d:=WardBin.basis_degree b
  have bound:(g₀*t₀⁻¹)^((F).grades b).2≤(2:ℝ)^d:=
    (pow_le_pow_left₀ pos.le gain _).trans (pow_le_pow_right₀ (by norm_num) rank)
  have linear: |phase (X b)|≤‖phase.toContinuousLinearMap‖*‖X b‖:=phase.toContinuousLinearMap.le_opNorm _
  rw [printed,abs_mul,abs_of_nonneg (pow_nonneg pos.le _),mul_assoc]
  exact mul_le_mul bound linear (abs_nonneg _) (pow_nonneg (by norm_num) _)

theorem top (ready:R.family.ref d≤N)(x:R.family.label d)(phase:ℂ→ₗ[ℝ]ℝ)(b:(F).Index):
    coin R N N per x phase b=fee R N per x phase (ConnectedActivityE6.Coat.gStep (R.family.beta N per)) b:=by
  have bare:Next.Rank.Price.columns (C) d N N per x=((C).factory d N per).terminal.symm x:=
    (R.makes.calibrated d N per ready).bare_coord _
  have rep:coefficients R N per x=(F).scaled ((B).threshold N)⁻¹ (Next.Rank.Price.awake (C) d N N per x):=by
    unfold coefficients Next.Rank.Price.awake
    rw [bare]
    funext j
    simp only [Pi.smul_apply,Labels.Frame.scaled_apply,smul_eq_mul]
    ring
  have temp:(R.family.path.rep N per N).beta=R.family.beta N per:=rfl
  rw [coin,fee,rep,temp]

end YM.Integration.WilsonOlderFreshPointDatedCoin
end
