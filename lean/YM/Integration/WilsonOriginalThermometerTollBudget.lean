import YM.Integration.WilsonOriginalThermometerTopGrading
import YM.Integration.WilsonMovingMentorRootRadius
import YM.Integration.WilsonRootedKioskPostRadius

/-! A cutoff- and period-uniform price for the actual 6/4/4 test aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerTollBudget
open Pressure Push.PriceCompiler
open Filter Finset Lattice Wilson RG Source Labels QuadraticLocal Earn Sunrise AllOrder AllOrder.Floe.Step
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRent
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopGrading
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)
local notation "A₀" => R.alloy.B.a
local notation "Y" n:max => R.alloy.B.a.clock.hatBeta n

def reach := univ.sup (fun z:Entry R levels => (raw R levels z).length)
def rate := max 1 ((1+mass R)*max 1 (wallet R levels 0))

private theorem stencil_pos (z:Entry R levels) : 0 ≤ stencil R levels z := by cases z <;> simp [stencil]

private theorem wallet_pos (σ:ℝ) : 0 ≤ wallet R levels σ :=
  sum_nonneg fun z _=>mul_nonneg (add_nonneg zero_le_one (mul_nonneg (positive ..).le (stencil_pos R z)))
    (Real.exp_nonneg _)

theorem rooted {β σ:ℝ} (one:1 ≤ β)
    (leases:∀z:Entry R levels, Real.exp (σ*(raw R levels z).length) ≤ β) :
    wallet R levels σ ≤ wallet R levels 0 * β^2 := by
  rw [wallet,wallet,Finset.sum_mul]
  apply sum_le_sum
  intro z _
  let t:=raw R levels z
  let a:=stencil R levels z
  let x:=Real.exp (σ*t.length)
  have non:0 ≤ t.magnitude:=sum_nonneg fun _ _=>abs_nonneg _
  have z0:0 ≤ a:=stencil_pos R z
  have terms:1+t.magnitude*x ≤ (1+t.magnitude)*β:=by
    calc 1+t.magnitude*x ≤ β+t.magnitude*β:=add_le_add one (mul_le_mul_of_nonneg_left (leases z) non)
         _ = _ := by ring
  have first:1+(1+t.magnitude*x)*a ≤ (1+(1+t.magnitude)*a)*β:=by
    calc 1+(1+t.magnitude*x)*a ≤ β+((1+t.magnitude)*β)*a:=add_le_add one (mul_le_mul_of_nonneg_right terms z0)
         _ = _ := by ring
  change (1+(1+t.magnitude*x)*a)*x ≤
    ((1+(1+t.magnitude*Real.exp (0*t.length))*a)*Real.exp (0*t.length))*β^2
  simp only [zero_mul,Real.exp_zero,mul_one]
  have b0:=zero_le_one.trans one
  exact (mul_le_mul first (leases z) (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)

theorem income (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ) (paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (m k:ℕ) (available:k ≤ (A₀).clock.J m) (width:reach R ≤ (A₀).clock.J m+1) :
    wallet R levels (Poetry.Agenda.seed D φ k ((A₀).clock.J m)) ≤ wallet R levels 0*(Y m)^2 := by
  let σ:=Poetry.Agenda.seed D φ k ((A₀).clock.J m)
  have one:1 ≤ Y m:=((A₀).fits.delayed m).le
  apply rooted R one
  intro z
  have path:(raw R levels z).length ≤ (A₀).clock.J m+1:=
    (Finset.le_sup (s:=Finset.univ) (f:=fun j=> (raw R levels j).length) (mem_univ z)).trans width
  apply (Real.exp_monotone ?_).trans (WilsonMovingMentorRootRadius.at_date (ψ:=φ) R D paid m k available)
  calc σ*((raw R levels z).length:ℝ) ≤ |σ| * ((raw R levels z).length:ℝ) :=
         mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
       _ ≤ |σ| * ((A₀).clock.J m+1:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast path) (abs_nonneg _)
       _ = _ := mul_comm .. 

theorem parameter (m:ℕ) : Advent.budgetR R m ≤ Y (m+1) := by
  have one:1 ≤ Y (m+1):=((A₀).fits.delayed (m+1)).le
  exact (min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le one
    (show Beaming.grain ((A₀).clock.J m) ≤ 1 by unfold Beaming.grain; apply (div_le_one (by positivity)).2; simp)).trans_eq (Real.rpow_one _))

theorem original (simple:G.Simple) (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ) (paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (i k:ℕ) (available:k ≤ (A₀).clock.J (i+1)) (width:reach R ≤ (A₀).clock.J (i+1)+1)
    {Ω:ℝ} (op:0 ≤ Ω) (feasible:Ω ≤ Advent.budgetR R i) :
    max 1 ((1+cap R i 1)*wallet R levels (Poetry.Agenda.seed D φ k ((A₀).clock.J (i+1))))*Ω ≤
      rate R*(Y (i+1))^11 := by
  let σ:=Poetry.Agenda.seed D φ k ((A₀).clock.J (i+1))
  let y:ℝ:=Y (i+1)
  let M:=mass R
  let C:=max 1 (wallet R levels 0)
  have one:1 ≤ y:=((A₀).fits.delayed (i+1)).le
  have y0:0 ≤ y:=zero_le_one.trans one
  have M0:0 ≤ M:=sum_nonneg fun _ _=>mul_nonneg (by unfold WilsonPositionThermometerStationNorm.cost; positivity) (by positivity)
  have C1:1 ≤ C:=le_max_left _ _
  have C0:=zero_le_one.trans C1
  have up:Y i ≤ Y (i+1):=by
    rw [beta_eq R.alloy.B.valid i]
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
      (Real.log_nonneg (Nat.one_le_cast.mpr (R.rolls.L _).property)))
  have coords: cap R i 1 ≤ M*y^8 := by
    simp only [cap,Real.rpow_one]
    calc (Y (i+1))^7*((Y i)*mass R) ≤ y^7*(y*M):=mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right up M0) (pow_nonneg y0 7)
         _ = _:=by ring
  have coord1:1+cap R i 1 ≤ (1+M)*y^8:=(add_le_add (show 1 ≤ y^8 from one_le_pow₀ one) coords).trans_eq (by ring)
  have wick:wallet R levels σ ≤ C*y^2:=(income R D φ paid (i+1) k available width).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg y0 _))
  have total: (1+cap R i 1)*wallet R levels σ ≤ rate R*y^10:=
    (mul_le_mul coord1 wick (wallet_pos R σ) (by positivity)).trans
      (calc (1+M)*y^8*(C*y^2) = ((1+M)*C)*y^10 := by ring
            _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg y0 _))
  have enough:1 ≤ rate R*y^10:=one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ one)
  exact (mul_le_mul (max_le enough total) (feasible.trans (parameter R i)) op
    (zero_le_one.trans enough)).trans_eq (by ring)

end YM.Integration.WilsonOriginalThermometerTollBudget
