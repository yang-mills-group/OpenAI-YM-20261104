import YM.Integration.WilsonOriginalMountedRegularFare

/-! A polynomial ratio of genuine Wilson meshes pays the count of dated regular errors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalCorridorLength
open Function Filter Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure Pert.Asymptotics
open scoped Topology

private theorem steps (S:Schedule)(b L:ℕ):(L:ℝ)*Real.log 3 ≤ S.scale (b+L)-S.scale b:=by
  induction L with
  | zero=>simp
  | succ L ih=>
    have floor:(3:ℝ) ≤ (S.block (b+L)).val:=by exact_mod_cast S.block_large (b+L)
    have logb:=Real.log_le_log (by norm_num : 0<(3:ℝ)) floor
    rw [show b+(L+1)=b+L+1 by omega,Schedule.scale_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    linarith only [ih,logb]

private theorem ratio (S:Schedule)(b K:ℕ):Real.log (S.a b/S.a K)=S.scale K-S.scale b:=by
  rw [Real.log_div (S.a_pos b).ne' (S.a_pos K).ne']
  simp only [Schedule.scale,Real.log_inv];ring

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

include simple in
theorem original (d:ℕ):
    ∀ᶠ b:ℕ in atTop,∀{L N per:ℕ},b+L ≤ N →
      R.family.S.a b/R.family.S.a (b+L) ≤ (H b)^d →
      let g:=regulatorRun R.family N per b
      0<g ∧ 3*g ≤ 1 ∧ (L:ℝ)*g ≤ 4*(d:ℝ)/Real.log 3:=by
  have grow:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [grow.eventually_ge_atTop 18] with b base
  intro L N per live re
  let h:=H b
  let β:=R.family.path.β N per b
  have hp:0<h:=by linarith only [base]
  have band:h/2 ≤ β:=(R.makes.wilson.represents N per b (by omega)).band.1
  have bp:0<β:=by linarith only [band,hp]
  have root:0<Real.sqrt β:=Real.sqrt_pos.mpr bp
  have thermal:3 ≤ Real.sqrt β:=(Real.le_sqrt (by norm_num) bp.le).mpr (by linarith only [band,base])
  have wlarge:0 ≤ Real.sqrt h:=Real.sqrt_nonneg h
  have compare:Real.sqrt h ≤ 2*Real.sqrt β:=by
    nlinarith only [Real.sq_sqrt hp.le,Real.sq_sqrt bp.le,band,root,wlarge]
  have logh:Real.log h ≤ 4*Real.sqrt β:=by
    have id:Real.log h=2*Real.log (Real.sqrt h):=by
      calc Real.log h=Real.log ((Real.sqrt h)^2):=by rw [Real.sq_sqrt hp.le]
           _ = _:=by rw [Real.log_pow];norm_num
    rw [id];linarith only [Real.log_le_self wlarge,compare]
  have reach:=Real.log_le_log (div_pos (R.family.S.a_pos b) (R.family.S.a_pos (b+L))) re
  rw [ratio,Real.log_pow] at reach
  have count:=le_trans (steps R.family.S b L) reach
  have wage: (L:ℝ)*Real.log 3 ≤ (d:ℝ)*(4*Real.sqrt β):=
    count.trans (mul_le_mul_of_nonneg_left logh (Nat.cast_nonneg d))
  change 0 < (Real.sqrt β)⁻¹ ∧ 3*(Real.sqrt β)⁻¹ ≤ 1 ∧
    (L:ℝ)*(Real.sqrt β)⁻¹ ≤ 4*(d:ℝ)/Real.log 3
  refine ⟨inv_pos.mpr root,?_,?_⟩
  · rw [←div_eq_mul_inv,div_le_iff₀ root,one_mul];exact thermal
  · rw [le_div_iff₀ (Real.log_pos (by norm_num:1<(3:ℝ)))]
    calc
      _ = ((L:ℝ)*Real.log 3)/Real.sqrt β:=by rw [div_eq_mul_inv];ring
      _ ≤ 4*(d:ℝ):=(div_le_iff₀ root).mpr (by linarith only [wage])

include simple in
theorem span (d b L:ℕ)(j:Fin L)(re:R.family.S.a b/R.family.S.a (b+L) ≤ (H b)^d):
    (j.val:ℝ) ≤ ((d:ℝ)/Real.log 3)*(1+Real.log (H (b+j.val)))^1:=by
  have h:=Real.log_le_log (div_pos (R.family.S.a_pos b) (R.family.S.a_pos (b+L))) re
  rw [ratio,Real.log_pow] at h
  have h0:0<H b:=zero_lt_one.trans (R.family.path.levels.fits.delayed b)
  have inc:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_add_right b j.val)
  have bound:Real.log (H b) ≤ 1+Real.log (H (b+j.val)):=by linarith only [Real.log_le_log h0 inc]
  have jp:(j.val:ℝ) ≤ L:=by exact_mod_cast j.isLt.le
  have logp:0<Real.log 3:=Real.log_pos (by norm_num)
  have cap:=((mul_le_mul_of_nonneg_right jp logp.le).trans ((steps R.family.S b L).trans h)).trans
    (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg d))
  calc
    _ ≤ ((d:ℝ)*(1+Real.log (H (b+j.val))))/Real.log 3:=(le_div_iff₀ logp).mpr cap
    _ = _:=by rw [pow_one];ring

end YM.Integration.WilsonOriginalPhysicalCorridorLength
end
