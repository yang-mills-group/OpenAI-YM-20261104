import YM.Integration.WilsonOriginalThermometerTollBudget

/-! Measure all seven first-return test radii in the same original held coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerRefund
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal Earn Sunrise ActualRunKernelPackets
open Pressure Push.PriceCompiler PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6
open WilsonOriginalThermometerTollBudget
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A₀" => R.alloy.B.a
local notation "Y" n:max => R.alloy.B.a.clock.hatBeta n
local notation "J" => Stock.census (Fin 3)

def cash := (2*rate R)*(4:ℝ)^19

private theorem cash_one : 1 ≤ cash R := by
  have h:1 ≤ rate R:=le_max_left _ _
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) h)
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))

include simple in
/-- The measured band at the upper nonbare date, before the volume. -/
theorem measured :
    ∀ᶠ i:ℕ in atTop, ∀p:ℕ,
      let g:=Coat.gStep (R.family.path.rep (i+2) p (i+1)).beta
      0<g ∧ g ≤ 1 ∧ (Y (i+2))*g^2 ≤ 4 ∧ (cash R)^3*g ≤ 1 := by
  let c:ℝ:=(cash R)^3
  have c1:1 ≤ c:=one_le_pow₀ (cash_one R)
  have c0:0 ≤ c:=zero_le_one.trans c1
  have warm:=((Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (2*c^2)
  have grow:=((tendsto_add_atTop_nat 1).eventually (RG01.Physical.nextHat simple (A₀)))
  filter_upwards [warm,grow] with i high grow p
  let β:ℝ:=(R.family.path.rep (i+2) p (i+1)).beta
  let z:=Real.sqrt β
  let g:=z⁻¹
  change 2*c^2 ≤ Y (i+1) at high
  change Y (i+2) ≤ 2*Y (i+1) at grow
  have band: (Y (i+1))/2 ≤ β:=(R.makes.wilson.represents (i+2) p (i+1) (by omega)).band.1
  have cb:c^2 ≤ β:=by linarith only [high,band]
  have bn:=le_trans (sq_nonneg c) cb
  have root:c ≤ z:=by simpa only [Real.sqrt_sq c0] using Real.sqrt_le_sqrt cb
  have zp:0<z:=zero_lt_one.trans_le (c1.trans root)
  have charge:c*g ≤ 1:=(mul_le_mul_of_nonneg_right root (inv_nonneg.mpr zp.le)).trans_eq (mul_inv_cancel₀ zp.ne')
  have gpos:0<g:=inv_pos.mpr zp
  have bin:β*g^2=1:=by
    change β*(Real.sqrt β)⁻¹^2=1
    rw [inv_pow,Real.sq_sqrt bn,mul_inv_cancel₀]
    have :0<β:=(sq_pos_of_pos (zero_lt_one.trans_le c1)).trans_le cb
    exact this.ne'
  change 0<g ∧ g ≤ 1 ∧ (Y (i+2))*g^2 ≤ 4 ∧ c*g ≤ 1
  refine ⟨gpos,(le_mul_of_one_le_left gpos.le c1).trans charge,?_,charge⟩
  calc (Y (i+2))*g^2 ≤ (4*β)*g^2:=mul_le_mul_of_nonneg_right (by linarith only [band,grow]) (sq_nonneg _)
       _ = _:=by rw [mul_assoc,bin,mul_one]

include simple in
theorem original :
    ∀ᶠ i:ℕ in atTop,∀ p:ℕ,
    let g:=Coat.gStep (R.family.path.rep (i+2) p (i+1)).beta
    ∀ b Ω h e:ℝ, 0<b → b ≤ rate R*(Y (i+2))^11 → 1 ≤ Ω → Ω ≤ Advent.budgetR R (i+1) → 1 ≤ h →
    h ≤ max 1 (max (Advent.budgetR R i*Advent.budgetR R (i+1)) e) → e ≤ 2 →
    ∀ w u:Fin 3→ℝ, (∀ v,w v=b⁻¹) → (∀ v,u v=w v/(Ω^6*h)) →
      (∀v,(u v)⁻¹ ≤ 2*rate R*(Y (i+2))^19) ∧ ∀s:(J).Mode,g^115 ≤ Poly.toll u s := by
  filter_upwards [measured R simple] with i band p g b Ω h e bp source rich affordable carried rest cheap w u before after
  let y:=Y (i+2)
  have y1:1 ≤ y:=((A₀).fits.delayed (i+2)).le
  have y0:=zero_le_one.trans y1
  have gp:0<g:=(band p).1
  have small:g ≤ 1:=(band p).2.1
  have close:y*g^2 ≤ 4:=(band p).2.2.1
  have coin:(cash R)^3*g ≤ 1:=(band p).2.2.2
  have next:Y (i+1) ≤ y:=by
    change Y (i+1) ≤ Y (i+1+1)
    rw [beta_eq R.alloy.B.valid (i+1)]
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
      (Real.log_nonneg (Nat.one_le_cast.mpr (R.rolls.L _).property)))
  have op:Ω ≤ y:=affordable.trans (parameter R (i+1))
  have step:Advent.budgetR R i * Advent.budgetR R (i+1) ≤ y^2:=
    (mul_le_mul ((parameter R i).trans next) (parameter R (i+1)) (zero_le_one.trans (Advent.budget_pos R)) y0).trans_eq
      (sq y).symm
  have y2:1 ≤ y^2:=one_le_pow₀ y1
  have reset:h ≤ 2*y^2:=rest.trans (max_le (by linarith only [y2])
    (max_le (by linarith only [step,y2]) (by linarith only [cheap,y2])))
  let X:=b*(Ω^6*h)
  have Ωp:0<Ω:=zero_lt_one.trans_le rich
  have hp:0<h:=zero_lt_one.trans_le carried
  have Xp:0<X:=mul_pos bp (mul_pos (pow_pos Ωp _) hp)
  have ret:Ω^6*h ≤ y^6*(2*y^2):=mul_le_mul (pow_le_pow_left₀ Ωp.le op _) reset hp.le (pow_nonneg y0 _)
  have amount:X ≤ 2*rate R*y^19:=(mul_le_mul source ret (mul_nonneg (pow_nonneg Ωp.le _) hp.le)
    (bp.le.trans source)).trans_eq (by ring)
  have same (v:Fin 3):u v=X⁻¹:=by simp [after v,before v,X,div_eq_mul_inv,mul_comm]
  have fee1:1 ≤ rate R:=le_max_left _ _
  have meter:X*g^38 ≤ cash R:=
    (mul_le_mul_of_nonneg_right amount (pow_nonneg gp.le _)).trans
      (calc 2*rate R*y^19*g^38 = 2*rate R*(y*g^2)^19 := by ring
            _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg y0 (sq_nonneg _)) close _)
              (mul_nonneg (by norm_num) (zero_le_one.trans fee1)))
  refine ⟨fun v=>by rw [same v, inv_inv]; exact amount,fun s=>?_⟩
  have n:s.val.card ≤ 3:=by simpa only [Fintype.card_fin] using (card_le_univ s.val)
  have powers: g^115 ≤ g*(g^38)^s.val.card:=
    (pow_le_pow_of_le_one gp.le small (show 38*s.val.card+1 ≤ 115 by omega)).trans_eq
      (by rw [pow_succ,pow_mul,mul_comm])
  have charged: g^115*X^s.val.card ≤ 1:=
    (mul_le_mul_of_nonneg_right powers (pow_nonneg Xp.le _)).trans
      (calc g*(g^38)^s.val.card*X^s.val.card = g*(X*g^38)^s.val.card:=by rw [mul_pow]; ring
            _ ≤ g*(cash R)^s.val.card:=mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg Xp.le (pow_nonneg gp.le _)) meter _) gp.le
            _ ≤ g*(cash R)^3:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (cash_one R) n) gp.le
            _ ≤ 1:=(mul_comm _ _).le.trans coin)
  simpa only [Poly.toll,same,prod_const,inv_pow,one_div] using (le_div_iff₀ (pow_pos Xp _)).mpr charged

end YM.Integration.WilsonOriginalThermometerRefund
