import YM.Integration.WilsonReceivedCloseTrailWallet
import YM.Integration.WilsonReceivedCloseSourceCalendar
import YM.Integration.WilsonReceivedOrdinaryPayment

/-! The measured-coupling budgets in the ordinary four-face price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOrdinaryScale
open Filter Lattice Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "H" => R.alloy.B.a.clock.hatBeta
theorem inverse {b N per i : ℕ} (ib : i ≤ b) (top : b < N)
    (calendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b) :
    (regulatorRun R.family N per (i+1))⁻¹ ≤ 3*(regulatorRun R.family N per b)⁻¹ := by
  have iN : i+1 ≤ N := by omega
  let z := R.family.path.β N per (i+1)
  let y := R.family.path.β N per b
  have hi := (R.makes.wilson.represents N per (i+1) iN).band.2
  have low := (R.makes.wilson.represents N per b top.le).band.1
  change z ≤ 2*H (i+1) at hi
  change H b/2 ≤ y at low
  have high := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec b calendar
  have rise := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le (Nat.succ_le_succ ib)
  have zp : 0 ≤ z := (Overlay.beta_positive R.makes.wilson iN).le
  have yp : 0 ≤ y := (Overlay.beta_positive R.makes.wilson top.le).le
  change ((Real.sqrt z)⁻¹)⁻¹ ≤ 3*((Real.sqrt y)⁻¹)⁻¹
  rw [inv_inv,inv_inv]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  nlinarith only [hi,low,high,rise,Real.sq_sqrt zp,Real.sq_sqrt yp,yp]

/-- The startup and trail have paid the fee for this actual occupied label. -/
theorem singleton {x t stage d w v fee : ℝ} (D : ℕ)
    (xp : 0<x) (dp : 0<d) (wp : 0<w) (fp : 0≤fee)
    (time : t⁻¹ ≤ 3*x⁻¹) (cap : stage^2*d ≤ x⁻¹)
    (label : 1 ≤ stage^2*(fee*(x⁻¹)^(2*D))*v) (actual : w=v/d) :
    (t*w)⁻¹ ≤ (3*fee)*(x⁻¹)^(2*D+2) := by
  have eq : v = w*d := (eq_div_iff dp.ne').mp actual |>.symm
  have ww : w⁻¹ ≤ x⁻¹*(fee*(x⁻¹)^(2*D)) := by
    rw [←one_div,div_le_iff₀ wp]
    calc
      _ ≤ stage^2*(fee*(x⁻¹)^(2*D))*(w*d) := eq ▸ label
      _ = (stage^2*d)*(fee*(x⁻¹)^(2*D))*w := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right cap (mul_nonneg fp (pow_nonneg (inv_nonneg.mpr xp.le) _))) wp.le
  calc
    _ = t⁻¹*w⁻¹ := by rw [mul_inv]
    _ ≤ (3*x⁻¹)*(x⁻¹*(fee*(x⁻¹)^(2*D))) := mul_le_mul time ww (inv_nonneg.mpr wp.le)
      (mul_nonneg (by norm_num) (inv_nonneg.mpr xp.le))
    _ = _ := by rw [pow_add]; ring

/-- Two extra comparator orders pay the two close-calendar losses when the loss is one. -/
theorem booked {x C : ℝ} (xp : 0 < x) (cold : x ≤ 1) (Cl : 0 ≤ C)
    {load q raw : ℕ} (enough : load+q+2 ≤ raw) :
    C*(x^(-(1:ℝ))*x^(-(1:ℝ)))*x^(raw-load) ≤ C*x^q := by
  rw [Real.rpow_neg_one]
  have degree := pow_le_pow_of_le_one xp.le cold (show q+2 ≤ raw-load by omega)
  calc
    _ ≤ C*(x⁻¹*x⁻¹)*x^(q+2) := mul_le_mul_of_nonneg_left degree
      (mul_nonneg Cl (mul_nonneg (inv_nonneg.mpr xp.le) (inv_nonneg.mpr xp.le)))
    _ = _ := by rw [pow_add]; field_simp

/-- The finite remainder and its two singleton factors are on the same received program. The
right side has one spare measured power at the reporter. -/
theorem finish {x t C M E ua ub err : ℝ} {r q h : ℕ}
    (xp : 0<x) (cold : 3*x≤1) (tp : 0<t) (temp : t≤3*x)
    (cp : 0≤C) (mp : 0≤M) (ep : 0≤E) (up : 0≤ua) (vp : 0≤ub)
    (income : E ≤ C*x^(q+1+h))
    (sa : ua ≤ M*(x⁻¹)^h) (sb : ub ≤ M*(x⁻¹)^h) (grade : q+1+2*h ≤ r+1)
    (prior : err ≤ E+E+E*(ub+E)+ua*E+t^(r+1)*(ua*ub)) :
    err ≤ (2*C+2*C*M+C^2+(3:ℝ)^(q+1+2*h)*M^2)*x^(q+1) := by
  have x1 : x≤1 := by linarith only [cold,xp]
  let j := q+1
  have positiveC : 0≤ C*x^(j+h) := mul_nonneg cp (pow_nonneg xp.le _)
  have positiveM : 0≤ M*(x⁻¹)^h := mul_nonneg mp (pow_nonneg (inv_nonneg.mpr xp.le) _)
  have easy : E≤C*x^j := income.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one xp.le x1 (Nat.le_add_right j h)) cp)
  have clear (k:ℕ) : x^(j+k)*(x⁻¹)^k = x^j := by rw [pow_add,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ xp.ne'),mul_one]
  have pair {u:ℝ} (un:0≤u) (cap:u≤M*(x⁻¹)^h) : E*u ≤ C*M*x^j := calc
    _ ≤ (C*x^(j+h))*(M*(x⁻¹)^h) := mul_le_mul income cap un positiveC
    _ = C*M*(x^(j+h)*(x⁻¹)^h) := by ring
    _ = _ := by rw [clear]
  have ee : E*E ≤ C^2*x^j := by
    calc
      _ ≤ (C*x^j)*(C*x^j) := mul_le_mul easy easy ep (mul_nonneg cp (pow_nonneg xp.le _))
      _ = C^2*x^j*x^j := by ring
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) (pow_nonneg xp.le _)) (pow_le_one₀ xp.le x1)
  have heat : t^(r+1) ≤ (3*x)^(j+2*h) := (pow_le_pow_left₀ tp.le temp _).trans
    (pow_le_pow_of_le_one (by positivity) cold grade)
  have tail : t^(r+1)*(ua*ub) ≤ (3:ℝ)^(j+2*h)*M^2*x^j := calc
    _ ≤ (3*x)^(j+2*h)*((M*(x⁻¹)^h)*(M*(x⁻¹)^h)) := mul_le_mul heat
      (mul_le_mul sa sb vp positiveM) (mul_nonneg up vp) (pow_nonneg (by positivity) _)
    _ = (3:ℝ)^(j+2*h)*M^2*(x^(j+2*h)*(x⁻¹)^(2*h)) := by rw [mul_pow,show 2*h=h+h by omega,pow_add (x⁻¹)]; ring
    _ = _ := by rw [clear]
  apply prior.trans
  rw [show E*(ub+E)=E*ub+E*E by ring,mul_comm ua E]
  calc
    _ ≤ C*x^j+C*x^j+(C*M*x^j+C^2*x^j)+C*M*x^j+((3:ℝ)^(j+2*h)*M^2*x^j) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add easy easy)
        (add_le_add (pair vp sb) ee)) (pair up sa)) tail
    _ = _ := by dsimp only [j]; ring

end YM.Integration.WilsonReceivedCloseOrdinaryScale
