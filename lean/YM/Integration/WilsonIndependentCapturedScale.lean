import YM.Integration.WilsonIndependentCapturedBand

/-! Pay the complete prescribed infrared meter in measured Wilson units
on the cofinal chosen band, uniformly in the physical ultraviolet cutoff
and period. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedScale
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Pert.Asymptotics WilsonIndependentCapturedCalendar WilsonIndependentCapturedBand
open WilsonPositionProgramReporterBand
open scoped Topology Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "H" => C.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda C.family.path.levels

def cost : ℝ := factor D * (1 + 3 / Real.log D.ratio)^2

private theorem logpos : 0 < Real.log (D.ratio:ℝ) := Real.log_pos
  (by exact_mod_cast ((by decide : 1 < 3).trans_le D.large))

private theorem factor_nonneg : 0 ≤ factor D := by
  unfold factor
  have := (logpos D).le
  have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
  positivity

theorem bounded (simple : G.Simple) : ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage,
    ∀ t, fare C D B.lower B.span B.powers t ≤ cost D * Λ (B.reporter+t)^4 := by
  obtain ⟨first,prices⟩ := paid C D simple
  refine ⟨first,?_⟩
  intro stage hs B t
  let height := Λ (B.reporter+t)
  have hone : 1 ≤ height := by
    have hot := Extension.UV.hat_positive simple C.alloy.B.a (B.reporter+t)
    change 1 < H (B.reporter+t) at hot
    change 1 ≤ 2 + Real.log (H (B.reporter+t))
    linarith [Real.log_nonneg hot.le]
  have pow : height^((3:ℝ)/2) ≤ height^2 := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hone (show (3:ℝ)/2 ≤ (2:ℕ) by norm_num)
  have paidIndex := B.ceiling t
  have large : height ≤ height^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hone) (zero_le_one.trans hone)]
  have small : (B.index t:ℝ) ≤ (3/Real.log D.ratio)*height^2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (logpos D)]
    change _ ≤ height^((3:ℝ)/2)+2*height at paidIndex
    linarith
  have core : 1+(B.index t:ℝ) ≤ (1+3/Real.log D.ratio)*height^2 := by nlinarith
  calc
    _ ≤ factor D * (1+(B.index t:ℝ))^2 := prices stage hs B t
    _ ≤ factor D * ((1+3/Real.log D.ratio)*height^2)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) core 2) (factor_nonneg D)
    _ = _ := by unfold cost; change _ = _*height^4; ring

private theorem polynomial (s : ℕ) {A : ℝ} (ha : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, A*(2+Real.log x)^s ≤ Real.sqrt (x/2) := by
  let C := 2*(1+A*3^s)
  have hc : 0 < C := by dsimp [C]; positivity
  have small := (isLittleO_log_rpow_rpow_atTop (s:ℝ) (show (0:ℝ) < 1/2 by norm_num)).def
    (inv_pos.mpr hc)
  filter_upwards [small,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with x hx hlog hpos
  change ‖Real.log x ^ (s:ℝ)‖ ≤ C⁻¹ * ‖x ^ ((1:ℝ)/2)‖ at hx
  rw [Real.rpow_natCast,← Real.sqrt_eq_rpow,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
  have each : 2+Real.log x ≤ 3*Real.log x := by linarith
  have hder := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) each s) ha
  rw [mul_pow] at hder
  have sale : C * (Real.log x)^s ≤ Real.sqrt x := by
    rwa [inv_mul_eq_div, le_div_iff₀ hc, mul_comm] at hx
  have half : A*(2+Real.log x)^s ≤ Real.sqrt x/2 := by
    dsimp [C] at sale
    nlinarith only [sale,hder,pow_nonneg (by linarith : 0 ≤ Real.log x) s]
  refine half.trans ?_
  rw [Real.sqrt_div hpos.le]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])

/-- One stage suffices for every finite output constant and degree.
Each numerical target has its own late reporting threshold on this band. -/
theorem uniform (simple : G.Simple) :
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage,
      ∀ {A : ℝ}, 0 ≤ A → ∀ power P debt : ℕ, ∀ᶠ t : ℕ in atTop,
    ∀ N per : ℕ, B.reporter+t ≤ N →
    let g := regulatorRun C.family N per (B.reporter+t)
    ∀ gross ratio : ℝ, gross ≤ (g^debt)⁻¹ → 0 ≤ ratio → ratio ≤ (g^(debt+P+1))^2 →
    A * (fare C D B.lower B.span B.powers t)^power * (gross * ratio^(1/2:ℝ)) ≤ g^P := by
  obtain ⟨first,purchase⟩ := bounded C D simple
  refine ⟨first,?_⟩
  intro stage hs B A ha power P debt
  have cg : 0 ≤ cost D := mul_nonneg (factor_nonneg D) (sq_nonneg _)
  have hot := (WardBin.bell C.family.path.levels simple).comp
    (tendsto_atTop_mono (fun t => Nat.le_add_left t B.reporter) tendsto_id)
  have hp := hot.eventually (polynomial (4*power) (A := A*(cost D)^power) (mul_nonneg ha (pow_nonneg cg power)))
  filter_upwards [hp] with t paid N per cut g gross ratio rent nonneg distance
  have hb := (C.makes.wilson.represents N per (B.reporter+t) cut).band.1
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le
    (div_pos (zero_lt_one.trans (Extension.UV.hat_positive simple C.alloy.B.a _)) (by norm_num)) hb))
  have fee : A*(fare C D B.lower B.span B.powers t)^power ≤ g⁻¹ := by
    have bound := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (fare_one C D B.lower B.span B.powers t))
      (purchase stage hs B t) power) ha
    rw [mul_pow,← pow_mul] at bound
    refine bound.trans ?_
    rw [← mul_assoc]
    refine paid.trans ?_
    change Real.sqrt _ ≤ ((Real.sqrt _)⁻¹)⁻¹
    rw [inv_inv]
    exact Real.sqrt_le_sqrt hb
  have root : ratio^(1/2:ℝ) ≤ g^(debt+P+1) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt distance).trans_eq (Real.sqrt_sq (pow_nonneg gp.le _))
  have coarse : gross * ratio^(1/2:ℝ) ≤ (g^debt)⁻¹ * g^(debt+P+1) :=
    (mul_le_mul_of_nonneg_right rent (Real.rpow_nonneg nonneg _)).trans
      (mul_le_mul_of_nonneg_left root (inv_nonneg.mpr (pow_nonneg gp.le _)))
  calc
    _ ≤ A*(fare C D B.lower B.span B.powers t)^power * ((g^debt)⁻¹*g^(debt+P+1)) :=
      mul_le_mul_of_nonneg_left coarse (mul_nonneg ha (pow_nonneg
        (zero_le_one.trans (fare_one C D B.lower B.span B.powers t)) _))
    _ ≤ g⁻¹*((g^debt)⁻¹*g^(debt+P+1)) := mul_le_mul_of_nonneg_right fee (by positivity)
    _ = g^P := by rw [pow_succ,pow_add]; field_simp

/-- Numerical fee before the measured cutoffs, even when the endpoints
of the two independently stopped infrared programs differ. -/
theorem funded (simple : G.Simple) {A : ℝ} (ha : 0 ≤ A) (power P debt : ℕ) :
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage, ∀ᶠ t : ℕ in atTop,
    ∀ N per : ℕ, B.reporter+t ≤ N →
    let g := regulatorRun C.family N per (B.reporter+t)
    ∀ gross ratio : ℝ, gross ≤ (g^debt)⁻¹ → 0 ≤ ratio → ratio ≤ (g^(debt+P+1))^2 →
    A * (fare C D B.lower B.span B.powers t)^power * (gross * ratio^(1/2:ℝ)) ≤ g^P := by
  obtain ⟨first,price⟩ := uniform C D simple
  exact ⟨first,fun stage hs B => price stage hs B ha power P debt⟩

end YM.Integration.WilsonIndependentCapturedScale

