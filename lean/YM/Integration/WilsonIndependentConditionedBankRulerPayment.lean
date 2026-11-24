import YM.Integration.WilsonIndependentConditionedBankClosing
import YM.Integration.WilsonIndependentConditionedGramSpatialCourse

/-! The change from the fine station to the physical reporting ruler spends a fixed power only on the high Taylor tail. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerPayment
open Filter RG Wilson PhysicalNext.Repeat.Legato
open WilsonIndependentConditionedGramSpatialCourse (Page)
open WilsonIndependentConditionedBankClosing (beta)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (T U q H E₀ E₁:ℕ)(P ε ξ B:ℝ)(gain:0 ≤ ξ)(nb:0 ≤ B)
    (low:P+ε+((2*E₀:ℕ):ℝ) ≤ ((2*T:ℕ):ℝ)*ξ)
    (high:P+ε+((2*(E₁+U*H):ℕ):ℝ) ≤ ((q+1:ℕ):ℝ)-((2*(T+1):ℕ):ℝ)*H):
    ∀ᶠ f:ℕ in atTop,∀(r:ℝ)(m p:ℕ)(accuracy:ℝ),
      let K:=berth R T f; let g:=thermal R f; let δ:=a K/a m
      Page R r m f K T U p accuracy → ∀X Y u:ℝ,X ≤ g^(-ε) → Y ≤ g^(-ε) → |u| ≤ B*g →
        X*(β f)^E₀*δ^ξ + Y*(β f)^E₁*(|u|^(q+1)*(δ^H)⁻¹) ≤ (1+B^(q+1))*g^P:=by
  filter_upwards [WilsonIndependentConditionedBankClosing.original R simple slow T q H E₀ (E₁+U*H)
    P ε ξ B gain nb low high] with f bill
  intro r m p accuracy K g δ page X Y u xx yy gross
  let df:=a K/a f
  have hot:0<g:=page.coupled.1
  have bp:0<β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have gap:0<df:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have home:0<a f/a m:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have mesh:δ=df*(a f/a m):=page.mesh
  have dp:0<δ:=by rw [mesh];exact mul_pos gap home
  have dd:δ ≤ df:=by rw [mesh];exact mul_le_of_le_one_right gap.le page.recess.2
  have paid:(a f/a m)⁻¹ ≤ (β f)^U:=by
    rw [beta,Real.rpow_neg hot.le,Real.rpow_natCast]
    exact (inv_le_inv₀ home (pow_pos hot _)).2 page.recess.1
  have inv:(δ^H)⁻¹ ≤ (β f)^(U*H)*(df^H)⁻¹:=by
    rw [mesh,mul_pow,mul_inv_rev,pow_mul,←inv_pow (a f/a m)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr home.le) paid H)
      (inv_nonneg.mpr (pow_nonneg gap.le _))
  calc
    _ ≤ (g^(-ε)*(β f)^E₀)*df^ξ + (g^(-ε)*(β f)^E₁)*(|u|^(q+1)*((β f)^(U*H)*(df^H)⁻¹)):=by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right xx (pow_nonneg bp.le _))
          (Real.rpow_le_rpow dp.le dd gain) (by positivity) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right yy (pow_nonneg bp.le _))
          (mul_le_mul_of_nonneg_left inv (by positivity)) (by positivity) (by positivity)
    _ = (g^(-ε)*(β f)^E₀)*df^ξ + (g^(-ε)*(β f)^(E₁+U*H))*(|u|^(q+1)*(df^H)⁻¹):=by
      rw [pow_add];ring
    _ ≤ _:=bill (g^(-ε)) (g^(-ε)) u le_rfl le_rfl gross

end YM.Integration.WilsonIndependentConditionedBankRulerPayment
