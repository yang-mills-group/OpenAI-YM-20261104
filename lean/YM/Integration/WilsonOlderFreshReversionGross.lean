import YM.Integration.WilsonOlderFreshFiledWord
import YM.Integration.WilsonCoherentMayerPublishedGross

/-! The signed kinetic reversion has its own rooted all-group tariff on the same original word list. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshReversionGross
open Function Finset Lattice Wilson RG Marker Ac Push QuadraticLocal QuadraticLocal.Earn
open Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Rebirth
open Chart AllOrder.Floe AllOrder.Floe.Step Comparison.RG02 QuadraticLocal.Affinity
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V ι W : Type} [DecidableEq V]
  {r : Census V} {p : Earn.Passport n V} (M : ι → Row p r G W) (B : BudgetPoint)
  (coin : Pace.Coin) (head : coin 0=0) (depth order : ℕ) (g t : ℝ)
  (w : V→ℝ) (grades : V→ℕ) {num shelf : ℕ} {pay ν z w₀ bill U α ξ : ℝ}
  (change : Recharged coin head g t depth order shelf pay ν z)
  (salary : Scene.Armada M w grades w₀ bill order num shelf)
  (fund : Invoice.Supports B U α g w₀ ξ) (pos : 0≤ν)
local notation "delta" => Mutation.defect M coin head depth order g t
local notation "debt" => Mutation.mend M B coin head depth order g t
local notation "allFee" => (Spill.allOver B)^(order+shelf+1)
local notation "inFee" => Invoice.price B U (order+shelf+1) num α ξ G

include change salary fund pos in
theorem original : WilsonRootedKioskOccupiedSlip.Gross debt w B.B α (allFee*(ν*inFee*bill)) := by
  have ga : 0≤allFee := pow_nonneg (zero_le_one.trans (Spill.allOver_ge B)) _
  have charge (j:ι) : 0≤(M j).charge B g :=
    mul_nonneg (mul_nonneg (by positivity) ((M j).real_quote B g).1) (M j).sound.le
  let e (j:ι) := |delta j| *(allFee*(M j).charge B g)
  refine ⟨e,(fun j=>mul_nonneg (abs_nonneg _) (mul_nonneg ga (charge j))),?_,?_⟩
  · intro j x U₁
    have full := Spill.nominal_price B g _ x (M j) (salary.honor j)
      (Scene.Armada.degreeR _ salary.toMinistry (M j) (salary.purchases.usable j)).2.2 U₁
    change ‖(delta j:ℂ)*(M j).nominal g x U₁‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left full (abs_nonneg _)
  intro v
  have valid:=Mutation.valid M coin head depth order w grades change salary
  have coeff (j:ι) : |delta j| *g^(M j).lamp.e≤ν := by
    have h:=change.earns _ (salary.purchases.usable j).1 (valid j).1
    rwa [abs_mul,abs_of_nonneg (pow_nonneg fund.1.le _),mul_comm] at h
  let f (j:ι) := if v∈(M j).ground B then
    |delta j| *Invoice.income B M w g j*Real.exp (α*coverNumber B.B ((M j).ground B)) else 0
  have package : SumBudget f (ν*inFee*bill) := by
    simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using Invoice.taxes B U M w salary.positive _
      num fund salary.suggests salary.purchases.spend (fun j=>(valid j).2.2) (fun j=>salary.quota _)
      delta ν pos coeff 0 v
  convert budget_scale ga package using 1
  ext j
  rw [show (debt).ground j=(M j).ground B from rfl]
  by_cases inGround : v∈(M j).ground B
  · simp only [inGround,if_true,f,e,Invoice.income]
    change Poly.toll w (M j).mode*(|delta j| *(allFee*(M j).charge B g))*_ = _
    ring
  · simp only [inGround,if_false,f,mul_zero]

end YM.Integration.WilsonOlderFreshReversionGross
