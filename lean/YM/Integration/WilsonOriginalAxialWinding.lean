import YM.Integration.WilsonOriginalMarkedEvaluation
import YM.QuadraticLocal.Fk.Fast

/-! The original marked winding estimate at the measured temperature on local axial fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalAxialWinding
open Filter Finset Lattice Wilson RG Tree Exterior Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison ConnectedActivityE6
open Laurent Stationary Comparison.RG02
open scoped Classical Topology

variable {G : Gauge}

/-- The original potential has the supremum norm on link and colour indices. -/
theorem axis {side : Side} (A : Link G side) {cap : ℝ} (positive : 0 ≤ cap)
    (inside : ∀ e, ‖Exterior.collect G (arm G side 1 A) e‖ ≤ cap) : ‖A‖ ≤ cap := by
  apply (pi_norm_le_iff_of_nonneg positive).2
  intro a
  let e : Edge (Site side) := (a.1,axisEquiv.symm a.2.1)
  have h := (PiLp.norm_apply_le (Exterior.collect G (arm G side 1 A) e) a.2.2).trans (inside e)
  change ‖A (a.1,axisEquiv (axisEquiv.symm a.2.1),a.2.2)‖ ≤ cap at h
  simpa only [axisEquiv.apply_symm_apply] using h

/-- At every later date the grade and the two numerical thresholds already hold, before choosing
    the cutoff, period, source face or local field. -/
def Open (R : Run G) (C M ε : ℝ) (arity d q h i : ℕ) : Prop :=
  let x := R.alloy.B.a.clock.hatBeta (i+1)
  let j := R.alloy.B.a.clock.J (i+1)
  1 ≤ x ∧ M ≤ x ∧ 2*C^arity*(2:ℝ)^q/ε ≤ x ∧ h+1 ≤ j ∧ d*arity+q+1 ≤ j

theorem eventually_open (R : Run G) (simple : G.Simple) (C M ε : ℝ) (arity d q h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ i ≥ m, Open R C M ε arity d q h i := by
  have warming : Tendsto R.alloy.B.a.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have stages : Tendsto R.alloy.B.a.clock.J atTop atTop := R.family.path.levels.fits.deep
  have full : ∀ᶠ t : ℕ in atTop, (1 : ℝ) ≤ R.alloy.B.a.clock.hatBeta t ∧
      M ≤ R.alloy.B.a.clock.hatBeta t ∧ 2*C^arity*(2:ℝ)^q/ε ≤ R.alloy.B.a.clock.hatBeta t ∧
      h+1 ≤ R.alloy.B.a.clock.J t ∧ d*arity+q+1 ≤ R.alloy.B.a.clock.J t := by
    filter_upwards [warming.eventually_ge_atTop 1, warming.eventually_ge_atTop M,
      warming.eventually_ge_atTop (2*C^arity*(2:ℝ)^q/ε), stages.eventually_ge_atTop (h+1),
      stages.eventually_ge_atTop (d*arity+q+1)] with t h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁,h₂,h₃,h₄,h₅⟩
  obtain ⟨t,paid⟩ := eventually_atTop.mp full
  filter_upwards [eventually_ge_atTop t] with m old
  intro i hi
  exact paid (i+1) (by omega)

private theorem restored {x g C ε scale W : ℝ} {arity d q r j : ℕ}
    (xp : 1 ≤ x) (g0 : 0 ≤ g) (band : x⁻¹ ≤ 2*g) (C₁ : 1 ≤ C) (ep : 0<ε)
    (budget : 2*C^arity*(2:ℝ)^q/ε ≤ x) (stage : d*arity+q+1 ≤ j)
    (rate : W ≤ x^(-(j:ℝ))) (sp : 0 ≤ scale) (salary : scale ≤ C*x^d) (face : r ≤ arity) :
    2*scale^r*W ≤ ε*g^q := by
  have px : 0<x := lt_of_lt_of_le zero_lt_one xp
  have big : 1 ≤ C*x^d := one_le_mul_of_one_le_of_one_le C₁ (one_le_pow₀ xp)
  have source := (pow_le_pow_left₀ sp salary r).trans (pow_le_pow_right₀ big face)
  have price : W ≤ (x^(d*arity+q+1))⁻¹ := by
    rw [Real.rpow_neg px.le, Real.rpow_natCast] at rate
    exact rate.trans ((inv_le_inv₀ (pow_pos px _) (pow_pos px _)).2 (pow_le_pow_right₀ xp stage))
  have tight : 2*C^arity*(2:ℝ)^q/x ≤ ε := by
    apply (div_le_iff₀ px).2
    simpa only [mul_comm x ε] using (div_le_iff₀ ep).1 budget
  calc 2*scale^r*W ≤ 2*scale^r*(x^(d*arity+q+1))⁻¹ := by
         exact mul_le_mul_of_nonneg_left price (mul_nonneg (by norm_num) (pow_nonneg sp _))
       _ ≤ 2*(C*x^d)^arity*(x^(d*arity+q+1))⁻¹ := by gcongr
       _ = (2*C^arity/x)*(x⁻¹)^q := by
         rw [mul_pow,←pow_mul,pow_succ,pow_add,inv_pow]
         field_simp
       _ ≤ (2*C^arity/x)*(2*g)^q := by gcongr
       _ = (2*C^arity*(2:ℝ)^q/x)*g^q := by rw [mul_pow]; ring
       _ ≤ ε*g^q := mul_le_mul_of_nonneg_right tight (pow_nonneg g0 _)

variable (R : Run G) {m i N per k : ℕ} (hk : Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) {φ : ℕ → ℕ} (law : VowsR.LawScroll G φ)
  (books : Mentor.Offices.Books D R.rolls Q φ) 
  (enrolled : VowsR.Chamber law R.kit D Q books)
  (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
  (hi : m ≤ i) (cut : i<N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (cost : ℝ) (cost0 : 0 ≤ cost) (cost1 : cost ≤ 1) (A : Link G (R.family.side i per))

local notation "x" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "fare" => Tutoring.bill R hk D Q π Γ books hi op lesson A cost

include enrolled fund cut cost0 cost1

/-- Cover winding on the actual measured nonbare course, after restoring each occupied test.
    Each original axial link is tested on its own physical period. -/
theorem measured (C M ε scale : ℝ) (arity d q h r : ℕ) (C₁ : 1 ≤ C) (M₀ : 0 ≤ M) (ep : 0<ε)
    (funded : Open R C M ε arity d q h i) (sp : 0 ≤ scale) (salary : scale ≤ C*x^d)
    (face : r ≤ arity) (inside : ∀ e, ‖Exterior.collect G (arm G (R.family.side i per) 1 A) e‖ ≤ M*x^h) :
    2*scale^r*fare ≤ ε*gf^q := by
  obtain ⟨xp,cap,budget,fieldGrade,priceGrade⟩ := funded
  have px : 0<x := lt_of_lt_of_le zero_lt_one xp
  have inside' := axis A (mul_nonneg M₀ (pow_nonneg px.le _)) inside
  have field : ‖A‖ ≤ x^(R.alloy.B.a.clock.J (i+1)) := calc
    ‖A‖ ≤ M*x^h := inside'
    _ ≤ x*x^h := mul_le_mul_of_nonneg_right cap (pow_nonneg px.le _)
    _ = x^(h+1) := by rw [pow_succ,mul_comm]
    _ ≤ _ := pow_le_pow_right₀ xp fieldGrade
  have seam := Tutoring.seam R hk D Q π Γ law books enrolled hi op lesson cost A fund cost1 cost0 field
  let β := (R.family.path.rep N per (i+1)).beta
  obtain ⟨lower,upper⟩ := (R.makes.wilson.represents N per (i+1) cut).band
  change x/2 ≤ β at lower
  change β ≤ 2*x at upper
  have warm : 0<β := lt_of_lt_of_le (by positivity) lower
  have sqrt_le : Real.sqrt β ≤ 2*x := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity,upper.trans (by nlinarith [mul_self_nonneg (x-1)])⟩
  have currency : x⁻¹ ≤ 2*gf := calc
    x⁻¹ = 2*(2*x)⁻¹ := by field_simp
    _ ≤ 2*gf := mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (by positivity) (Real.sqrt_pos.2 warm)).2 sqrt_le) (by norm_num)
  exact restored xp (inv_nonneg.2 (Real.sqrt_nonneg β)) currency C₁ ep budget priceGrade seam sp salary face

end YM.Integration.WilsonOriginalAxialWinding
