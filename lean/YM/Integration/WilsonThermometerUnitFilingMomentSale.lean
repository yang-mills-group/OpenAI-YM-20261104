import YM.Integration.WilsonOriginalCoveredMixedRoster
/-! The actual suspended compound salaries pay any fixed positive-rank
root moment with a single arbitrarily small before-cutoff coupling power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingMomentSale
open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Stationary
open WilsonOriginalSuspendedTensor WilsonEmittedRootedJetWage
open scoped Classical BigOperators

def positionCost (u:ℕ)(σ:ℝ):ℝ:=(4/σ)^u*(u.factorial:ℝ)*Real.exp 1

theorem position {σ:ℝ}(positive:0<σ)(small:σ ≤ 1)(s:ℕ)(u:ℕ):
    (1+2*(s:ℝ))^u ≤ positionCost u σ*Real.exp (σ*s/2):=by
  let z:ℝ:=σ*(1+2*(s:ℝ))/4
  have z0:0 ≤ z:=by dsimp [z];positivity
  have raw:=Real.pow_div_factorial_le_exp z z0 u
  have paid:z^u ≤ Real.exp z*(u.factorial:ℝ):=(div_le_iff₀ (by positivity)).mp raw
  have eq:1+2*(s:ℝ)=(4/σ)*z:=by dsimp [z]; field_simp
  have zz:z=σ/4+σ*s/2:=by dsimp [z];ring
  have emax:Real.exp z ≤ Real.exp 1*Real.exp (σ*s/2):=by
    rw [zz,Real.exp_add];gcongr;linarith
  rw [eq,mul_pow]
  calc
    _ ≤ (4/σ)^u*(Real.exp z*(u.factorial:ℝ)):=by gcongr
    _ ≤ (4/σ)^u*((Real.exp 1*Real.exp (σ*s/2))*(u.factorial:ℝ)):=by gcongr
    _ = _:=by unfold positionCost;ring

theorem window (G:Gauge)(r:ℕ){σ:ℝ}(positive:0<σ)(small:σ ≤ 1):
    fee G σ r ≤ fee G 1 r * (σ⁻¹)^(4*r+r):=by
  let A:=2*(G.colorScale*(WilsonOriginalGroupInkDirections.weight G*r))
  have inv:1 ≤ σ⁻¹:=one_le_inv₀ positive |>.mpr small
  have cover: max 1 (A/σ) ≤ max 1 (A/1)*σ⁻¹:=by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left ..) inv
    · rw [div_one, div_eq_mul_inv];exact mul_le_mul_of_nonneg_right (le_max_right ..) (inv_nonneg.mpr positive.le)
  have div:2/(σ/2)=4*σ⁻¹:=by field_simp;ring
  have ex:Real.exp (σ/2/2) ≤ Real.exp ((1:ℝ)/2/2):=by gcongr
  have pr:0 ≤ WilsonMarkedAngularTestInvoice.fee r r:=WilsonMarkedAngularTestInvoice.fee_nonnegative ..
  unfold fee WilsonOriginalResidentAngles.fare WilsonOriginalSuspendedWord.price
  change _*(_*_*max 1 (A/σ)^r) ≤ _*(_*_*max 1 (A/1)^r)*_
  rw [div]
  calc
    _ ≤ ((Fintype.card (Loc G 1)+1:ℝ)^r*(4*σ⁻¹)^(4*r)*
      ((4*r).factorial:ℝ)*Real.exp ((1:ℝ)/2/2))*
      (WilsonMarkedAngularTestInvoice.fee r r*(max 1 (r:ℝ))^r*(max 1 (A/1)*σ⁻¹)^r):=by
        push_cast
        gcongr
    _ = _:=by push_cast;norm_num only;rw [mul_pow,mul_pow,pow_add];ring

theorem power {σ β δ:ℝ}(positive:0<σ)(small:σ ≤ 1)(tiny:0<δ)
    (bought:Real.exp (σ⁻¹^2) ≤ β)(h:ℕ):
    σ⁻¹^h ≤ ((h.factorial:ℝ)/δ^h)*β^δ:=by
  have inv:1 ≤ σ⁻¹:=(one_le_inv₀ positive).mpr small
  have move:σ⁻¹ ≤ σ⁻¹^2:=by nlinarith
  have betale:0<β:=(Real.exp_pos _).trans_le bought
  have value:Real.exp (δ*σ⁻¹^2) ≤ β^δ:=by
    rw [mul_comm,Real.exp_mul];gcongr
  have tay:=Real.pow_div_factorial_le_exp (δ*σ⁻¹^2) (by positivity) h
  have cap:(δ*σ⁻¹^2)^h ≤ β^δ*(h.factorial:ℝ):=
    ((div_le_iff₀ (show 0<(h.factorial:ℝ) by positivity)).mp tay).trans (by gcongr)
  calc
    _ ≤ (σ⁻¹^2)^h:=by gcongr
    _ ≤ ((h.factorial:ℝ)/δ^h)*β^δ:=by
      rw [mul_pow] at cap
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos tiny h)]
      rw [mul_comm _ (δ^h),mul_comm (h.factorial:ℝ)]
      exact cap

def price (G:Gauge)(r u:ℕ)(δ:ℝ):ℝ:=
  fee G 1 r*positionCost u 1*((4*r+r+u).factorial:ℝ)/δ^(4*r+r+u)

theorem original (G:Gauge)(r u:ℕ){σ β δ:ℝ}(positive:0<σ)(small:σ ≤ 1)(tiny:0<δ)
    (bought:Real.exp (σ⁻¹^2) ≤ β):
    fee G σ r*positionCost u σ ≤ price G r u δ*β^δ:=by
  have step:=window G r positive small
  have pos:0 ≤ fee G 1 r:=(nonnegative G one_pos r)
  have loc:positionCost u σ=positionCost u 1*(σ⁻¹)^u:=by
    unfold positionCost
    rw [div_eq_mul_inv,mul_pow,div_one]
    ring
  rw [loc]
  calc
    _ ≤ (fee G 1 r*σ⁻¹^(4*r+r))*(positionCost u 1*σ⁻¹^u):=by
      gcongr;unfold positionCost;positivity
    _ = (fee G 1 r*positionCost u 1)*(σ⁻¹)^(4*r+r+u):=by rw [pow_add];ring
    _ ≤ _ := by
      have pw:=power positive small tiny bought (4*r+r+u)
      calc
        _ ≤ (fee G 1 r*positionCost u 1)*(((4*r+r+u).factorial:ℝ)/δ^(4*r+r+u)*β^δ):=by
          gcongr;unfold positionCost;positivity
        _ = _:=by unfold price;ring

end YM.Integration.WilsonThermometerUnitFilingMomentSale
