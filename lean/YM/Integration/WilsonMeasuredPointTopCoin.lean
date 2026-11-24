import YM.Integration.WilsonMeasuredPointStride
import YM.Integration.WilsonNeutralNominatedRopes

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointTopCoin
open Lattice RG Wilson Labels Next.Foundations
open PhysicalNext.Repeat.Legato WilsonNeutralCopiedField WilsonNeutralCopiedProgram WilsonNeutralCutoffAlphabet
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (N per:ℕ)
local notation "C" => R.family
local notation "F" => R.family.labels.level 4
local notation "B" => R.family.path.levels.clock
local notation "g₀" => ConnectedActivityE6.Coat.gStep (R.family.beta N per)
local notation "t₀" => (B).threshold N

/-- The original cutoff ratio for any admitted period, including both sources of scale. -/
theorem ratio : 0 < g₀*t₀⁻¹ ∧ (g₀*t₀⁻¹)^2≤2 := by
  let H:ℝ:=(B).hatBeta N
  let β:=R.family.beta N per
  let m:ℝ:=(B).monitor N
  have hp:0<H:=zero_lt_one.trans (R.alloy.B.a.fits.delayed N)
  have bp:0<β:=Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=per) le_rfl
  have band:H/2≤β:=(R.makes.wilson.represents N per N le_rfl).band.1
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

theorem birth (ready:R.family.ref 4≤ N)(x:R.family.label 4):
    coefficients R N per x=(F).scaled t₀⁻¹ (Next.Rank.Price.awake (C) 4 N N per x) := by
  have bare:Next.Rank.Price.columns (C) 4 N N per x=((C).factory 4 N per).terminal.symm x:=
    (R.makes.calibrated 4 N per ready).bare_coord _
  unfold coefficients Next.Rank.Price.awake
  rw [bare]
  funext j
  simp only [Pi.smul_apply,Labels.Frame.scaled_apply,smul_eq_mul]
  ring

theorem wage (ready:R.family.ref 4≤ N)(x:R.family.label 4)(phase:ℂ→ₗ[ℝ]ℝ)(j:(F).Index):
    fee R N per x phase g₀ j=(g₀*t₀⁻¹)^((F).grades j).2*phase ((Next.Rank.Price.awake (C) 4 N N per x) j) := by
  rw [fee,birth R N per ready,Labels.Frame.scaled_apply]
  rw [← Complex.real_smul,map_smul,smul_eq_mul,mul_pow]
  ring

theorem funded (simple:G.Simple)(ready:R.family.ref 4≤ N)(x:R.family.label 4)(phase:ℂ→ₗ[ℝ]ℝ):
    (∑j:(F).Index,|fee R N per x phase g₀ j|)≤2*‖phase.toContinuousLinearMap‖*
      (F).coeffSize (Next.Rank.Price.awake (C) 4 N N per x) := by
  have ⟨positive,cap⟩:=ratio R N per
  let X:=Next.Rank.Price.awake (C) 4 N N per x
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _=>?_
  have exponent:(g₀*t₀⁻¹)^((F).grades j).2≤2:=by
    by_cases h:j=0
    · subst j;rw [(F).zero_degree];norm_num
    · rw [WilsonNeutralBilinearCoordinates.classification simple (F) j h];exact cap
  have linear: |phase (X j)|≤‖phase.toContinuousLinearMap‖*‖X j‖:=
    phase.toContinuousLinearMap.le_opNorm _
  rw [wage R N per ready,abs_mul,abs_of_nonneg (pow_nonneg positive.le _)]
  exact (mul_le_mul exponent linear (abs_nonneg _) (by norm_num)).trans_eq (mul_assoc ..).symm

/-- Every degree-zero position of the literal nominated cutoff field, unit included. -/
theorem nominated (A:WilsonPositionThermometerCapStation.Group R.family 6)(leg:Fin 2)(phase:ℂ→ₗ[ℝ]ℝ)
    (j:(F).Index):
    WilsonNeutralNominatedRopes.planted R A N per leg phase (WilsonNeutralBilinearLetters.plain (F) j)=
      PowerSeries.C (fee R N per (WilsonNeutralOffsetCutoff.named R A N per leg.succ) phase g₀ j) := by
  unfold WilsonNeutralNominatedRopes.planted
  rw [point_eq (F) j]
  unfold submitted
  rw [show WilsonCoeffUV.Cosmos.sheet (F) (point (F) j)=j from rfl,if_pos rfl]
  rfl

end YM.Integration.WilsonMeasuredPointTopCoin
end
