import YM.Integration.WilsonOriginalThermometerRefund
import YM.Integration.WilsonOriginalThermometerReportedToll

/-! The first nonbare held coupling pays all three measured apertures from the nominated report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerReportedRefund
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal Earn Sunrise ConnectedActivityE6
open Pressure Push.PriceCompiler PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalThermometerTollBudget
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A₀" => R.alloy.B.a
local notation "Y" n:max => R.alloy.B.a.clock.hatBeta n
local notation "J" => Stock.census (Fin 3)

private def cash := (2*rate R)*(4:ℝ)^26

private theorem cash_one : 1 ≤ cash R :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) (le_max_left _ _))
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))

include simple in
theorem small (C:ℝ) (pos:0 ≤ C) :
    ∀ᶠ i:ℕ in atTop, ∀p:ℕ, C*Coat.gStep (R.family.path.rep (i+2) p (i+1)).beta ≤ 1 := by
  have growth:=((Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (2*(max 1 C)^2)
  filter_upwards [growth] with i high p
  let β:ℝ:=(R.family.path.rep (i+2) p (i+1)).beta
  have lo:(Y (i+1))/2 ≤ β:=(R.makes.wilson.represents (i+2) p (i+1) (by omega)).band.1
  change 2*(max 1 C)^2 ≤ Y (i+1) at high
  have paid:(max 1 C)^2 ≤ β:=by linarith only [high,lo]
  have c0:0 ≤ max 1 C:=pos.trans (le_max_right _ _)
  have price:max 1 C ≤ Real.sqrt β:=by simpa only [Real.sqrt_sq c0] using Real.sqrt_le_sqrt paid
  have root:0<Real.sqrt β:=zero_lt_one.trans_le ((le_max_left _ _).trans price)
  exact (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans price) (inv_nonneg.mpr root.le)).trans_eq (mul_inv_cancel₀ root.ne')

include simple in
theorem original :
    ∀ᶠ i:ℕ in atTop,∀ p:ℕ,
    let g:=Coat.gStep (R.family.path.rep (i+2) p (i+1)).beta
    ∀ b Ω h e:ℝ, 0<b → b ≤ rate R*(Y (i+2))^18 → 1 ≤ Ω → Ω ≤ Advent.budgetR R (i+1) → 1 ≤ h →
    h ≤ max 1 (max (Advent.budgetR R i*Advent.budgetR R (i+1)) e) → e ≤ 2 →
    ∀ w u:Fin 3→ℝ,(∀v,w v=b⁻¹) → (∀v,u v=w v/(Ω^6*h)) →
      (∀v,(u v)⁻¹ ≤ 2*rate R*(Y (i+2))^26) ∧ ∀s:(J).Mode,g^157 ≤ Poly.toll u s := by
  filter_upwards [WilsonOriginalThermometerRefund.original R simple, WilsonOriginalThermometerRefund.measured R simple,
    small R simple ((cash R)^3) (pow_nonneg (zero_le_one.trans (cash_one R)) _)] with i refunded measured credit
    p g b Ω h e bp birth rich feasible alive rerent unit w u orig next
  let y:=Y (i+2)
  have yp:0<y:=zero_lt_one.trans_le ((A₀).fits.delayed (i+2)).le
  have paid:b/y^7 ≤ rate R*y^11:=(div_le_iff₀ (pow_pos yp _)).2 (birth.trans_eq (by ring))
  let f:Fin 3→ℝ:=fun _=>(b/y^7)⁻¹
  let t:Fin 3→ℝ:=fun v=>f v/(Ω^6*h)
  have first:=(refunded p (b/y^7) Ω h e (div_pos bp (pow_pos yp _)) paid rich feasible alive rerent unit
    f t (fun _=>rfl) (fun _=>rfl)).1
  let X:=b*(Ω^6*h)
  have Ωp:=zero_lt_one.trans_le rich
  have hp:=zero_lt_one.trans_le alive
  have Xp:0<X:=mul_pos bp (mul_pos (pow_pos Ωp _) hp)
  have price:X ≤ 2*rate R*y^26:=by
    calc X = (t 0)⁻¹*y^7:=by dsimp [t,f,X]; field_simp [bp.ne',yp.ne',Ωp.ne',hp.ne']
         _ ≤ (2*rate R*y^19)*y^7:=mul_le_mul_of_nonneg_right (first 0) (pow_nonneg yp.le _)
         _ = _:=by ring
  have same (v:Fin 3):u v=X⁻¹:=by simp [next v,orig v,X,div_eq_mul_inv,mul_comm]
  have gp:0<g:=(measured p).1
  have gu:g ≤ 1:=(measured p).2.1
  have score:X*g^52 ≤ cash R:=(mul_le_mul_of_nonneg_right price (pow_nonneg gp.le _)).trans
    (calc 2*rate R*y^26*g^52=2*rate R*(y*g^2)^26:=by ring
          _ ≤ _:=mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg yp.le (sq_nonneg _)) (measured p).2.2.1 26)
            (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))))
  refine ⟨fun v=>by rw [same v,inv_inv]; exact price,fun s=>?_⟩
  have n:s.val.card ≤ 3:=by simpa only [Fintype.card_fin] using (card_le_univ s.val)
  have powers:g^157 ≤ g*(g^52)^s.val.card:=
    (pow_le_pow_of_le_one gp.le gu (show 52*s.val.card+1 ≤ 157 by omega)).trans_eq
      (by rw [pow_succ,pow_mul,mul_comm])
  have closed:g^157*X^s.val.card ≤ 1:=
    (mul_le_mul_of_nonneg_right powers (pow_nonneg Xp.le _)).trans
      (calc g*(g^52)^s.val.card*X^s.val.card=g*(X*g^52)^s.val.card:=by rw [mul_pow];ring
            _ ≤ g*(cash R)^s.val.card:=mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg Xp.le (pow_nonneg gp.le _)) score _) gp.le
            _ ≤ g*(cash R)^3:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (cash_one R) n) gp.le
            _ ≤ 1:=(mul_comm _ _).le.trans (credit p))
  simpa only [Poly.toll,same,prod_const,inv_pow,one_div] using (le_div_iff₀ (pow_pos Xp _)).mpr closed

end YM.Integration.WilsonOriginalThermometerReportedRefund
