import YM.Integration.WilsonThermometerSameWalkBare
import YM.Integration.WilsonThermometerSameWalkBirthCurrency
import YM.Integration.WilsonThermometerSameWalkMotion

/-! Arbitrary-order true bare entrance to the originally enrolled marked
Wilson tower, at arbitrary support, with its literal occupied hard stock. -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkBareField
open Function Filter Lattice RG Wilson Labels Source RG.Shoot
open PhysicalNext Repeat Legato Graces Roost Org Pressure Testing Precision Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open Trace.Physical ProjectorNext.Equivariance RG05Readout Native Address Many
open Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level d
local notation "S₀" => R.family.localSection d
local notation "A₀" => R.family.params
local notation "H₀" i:max => (L₀).clock.hatBeta i
local notation "c₀" => WilsonThermometerSameWalkBirthCurrency.upper (G:=G) d

theorem original (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d) (ord:ℕ) {ε:ℝ} (acc:0 < ε) :
    ∀ᶠ N:ℕ in atTop, ∀ (per m k:ℕ) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ j,Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ N →
    Topline (Ψ N) ((L₀).clock.forcedAllowance N) →
    ∀ (z:Site (R.family.side N per)) (v:R.family.label d),
    ∃ Z:Coefficient (F₀) (R.family.side N per), Z.Format z A₀ (Ψ N) ∧
      Z.remBound z (Ψ N) (LocalComparison.forcedDivisor R.family N)
        (ε*((H₀ N)^ord)⁻¹*(1+(F₀).coeffSize v)) ∧
      Z.density z S₀ (Ψ N)=WilsonThermometerSameWalkMotion.field R z (Nat.le_refl N) v:=by
  filter_upwards [WilsonThermometerSameWalkBirthCurrency.original R d simple M ord acc] with N funded
  intro per m k π Γ Ψ course beginAt roof z v
  let P:= Ψ N
  have law:=QuadraticLocal.Advent.later R π Γ Ψ course beginAt (Nat.le_refl N)
  have shape:P.p=(L₀).budget N:=law.truep.point
  have κpos:0 < (L₀).clock.forcedAllowance N:=Real.exp_pos _
  let B:=fullCost (F₀) P.p (c₀)*(F₀).coeffSize ((F₀).core v)
  have hb:1 ≤ c₀:=(Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have budget:∀ U,‖supplement (S₀) P z v U‖ ≤ B:=supplement_bound (S₀) P z (R.makes.sections d) hb
    (fun u U=>(Next.Foundations.full_value_bound (G:=G) d).choose_spec.2 u |>.2 _ z U) v
  have b0:0 ≤ B:=(norm_nonneg _).trans (budget 1)
  let e:=Real.exp ((P.p.supportExponent+1)*coverNumber P.p.B ((S₀).footprint z))
  let slack:=QuadraticLocal.Willow.haloSlack P.p.B
  have pos:0 < slack:=by unfold slack QuadraticLocal.Willow.haloSlack QuadraticLocal.Willow.area;positivity
  let w:=slack/(1+B*e)
  have ep:0 ≤ e:=(Real.exp_pos _).le
  have den:0 < 1+B*e:=by positivity
  have cash:0 < w:=div_pos pos den
  have win:w*B*e ≤ slack:=by
    unfold w;rw [mul_assoc,div_mul_eq_mul_div,div_le_iff₀ den];nlinarith only [pos]
  obtain ⟨Z,ok,pay,full⟩:=WilsonThermometerSameWalkBare.original P (S₀) (R.makes.sections d) z v
    cash κpos b0 budget win law.truep.valid roof
  have wage:w⁻¹=WilsonThermometerSameWalkBirthCurrency.fee R d N z v:=by
    unfold w WilsonThermometerSameWalkBirthCurrency.fee B slack e
    rw [shape,inv_div,div_eq_inv_mul]
  have refund:=funded z v
  refine ⟨Z,ok,rem_mono pay (wage ▸ refund),funext fun U=>(full U).trans ?_⟩
  exact (WilsonThermometerSameWalkMotion.top R π Γ Ψ course beginAt z v U).symm

end YM.Integration.WilsonThermometerSameWalkBareField
end
