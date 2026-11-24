import YM.Integration.WilsonMarkedFixedPoleGross

/-! The polynomial capital of the unmasked captured ordinary source is paid
from its actual Armada at the elected teacher's aperture. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRRows
open Function Filter Finset Lattice Wilson RG Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Poetry
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{V X ι:Type}[DecidableEq V]{P:Passport n V}{J:Census V}

theorem board {g:ℝ}{I:ℝ}(gp:0<g)(small:g≤1)
    (M:ι→Row P J G X)(w:V→ℝ)(t:V→ℕ)(p:BudgetPoint){U σ C ξ:ℝ}{q k h D E:ℕ}
    (L:Scene.Armada M w t σ C q k h)(scope:Invoice.Supports p U (p.supportExponent+2) g σ ξ)
    (pole:∀s:J.Mode,(∑v∈s.val,t v)+1≤D)
    (salary:C≤I*(3*g⁻¹)^E)
    (rate:Invoice.price p U (q+h+1) k (p.supportExponent+2) ξ G≤(2:ℝ)^(q+h+1)*(3*g⁻¹)^2):
    let levy:=(2:ℝ)^(q+h+1)
    let K:=levy^2*max 1 I
    let e:=D+2+E
    ∃C₀ C₁:ℝ,0≤C₀ ∧ 0≤C₁ ∧ C₀≤K*(3*g⁻¹)^e ∧ C₁≤K*(3*g⁻¹)^e ∧
      (rendered M p g).Paid w p.B (p.supportExponent+2) C₀ ∧
      Gross (rendered M p g) w p.B (p.supportExponent+2) C₁:=by
  let x:=3*g⁻¹
  let levy:=(2:ℝ)^(q+h+1)
  let fee:=Invoice.price p U (q+h+1) k (p.supportExponent+2) ξ G
  have z:0<fee:=Invoice.positive p U (q+h+1) scope.2.2.1 k scope.2.2.2.2.2.2.1 G
  have Cpos:0≤C:=budget_nonneg (L.suggests 0)
  have xone:1≤x:=by
    have pay:1≤g⁻¹:=by rw [←one_div];exact (le_div_iff₀ gp).mpr (by simpa using small)
    dsimp only [x];linarith
  have vone:1≤levy:=one_le_pow₀ (by norm_num)
  have inv:g⁻¹≤x:=by dsimp only [x];linarith only [inv_pos.mpr gp]
  have cash:fee*C≤levy*max 1 I*x^(2+E):=by
    calc
      _≤(levy*x^2)*(I*x^E):=mul_le_mul rate salary Cpos (by positivity)
      _=levy*I*x^(2+E):=by rw [pow_add];ring
      _≤_:=by gcongr;exact le_max_right _ _
  have cash₀:0≤fee*C:=mul_nonneg z.le Cpos
  let bound:=levy^2*max 1 I*x^(D+2+E)
  have high:(levy/g^D)*(fee*C)≤ bound:=by
    calc
      _≤(levy*x^D)*(levy*max 1 I*x^(2+E)):=by
        apply mul_le_mul _ cash cash₀ (by positivity)
        rw [div_eq_mul_inv,←inv_pow];gcongr
      _=bound:=by dsimp only [bound];rw [show D+2+E=D+(2+E) by omega,pow_add];ring
  have low:fee*C≤bound:=by
    apply le_trans _ high
    apply le_mul_of_one_le_left cash₀
    exact (one_le_div (pow_pos gp _)).mpr ((pow_le_one₀ gp.le small).trans vone)
  exact ⟨fee*C,_,cash₀,mul_nonneg (div_nonneg (zero_le_one.trans vone) (pow_nonneg gp.le _)) cash₀,
    low,high,Scene.Armada.paid M w t L p scope,WilsonMarkedFixedPoleGross.landed M w t p L scope D pole⟩

end YM.Integration.WilsonOriginalTwoFlatIRRows
