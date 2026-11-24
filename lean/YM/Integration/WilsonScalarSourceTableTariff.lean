import YM.Integration.WilsonScalarSourceTableFields
import YM.Integration.ManuscriptQLocalScalarDirections

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonScalarSourceTableTariff
open Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open Push.PriceCompiler WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Marker PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "c₀" => R.family.side d.level d.period
local notation "E" => Vec G c₀ 1
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

theorem absorb {κ x W V τ ρ target : ℝ} (hκ : 0 < κ) (hW : 0 ≤ W) (hτ : 0 ≤ τ) (hV : τ ≤ V)
    (paid : abs (V*W*abs ρ*Real.exp 1) * Real.exp (-κ*(till x:ℝ)) ≤ target) :
    τ*(W*(ρ*Real.exp (-(2*κ)*(till x:ℝ)))) ≤ target*Real.exp (-((min κ 1)/100000)*(radiusB x:ℝ)) := by
  let e := Real.exp (-κ*(till x:ℝ))
  let B := Real.exp (-((min κ 1)/100000)*(radiusB x:ℝ))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hr : e ≤ Real.exp 1 * B := by
    simpa only [abs_one,one_mul] using ManuscriptQLocalScalarDirections.price_radius_polynomial κ x 1 hκ.le
  have hVW : 0 ≤ V*W*abs ρ := mul_nonneg (mul_nonneg (hτ.trans hV) hW) (abs_nonneg _)
  have hpay : (V*W*abs ρ*Real.exp 1)*e ≤ target := by
    simpa only [abs_of_nonneg (mul_nonneg hVW (Real.exp_pos 1).le)] using paid
  have hs : τ*W*ρ ≤ V*W*abs ρ :=
    (mul_le_mul_of_nonneg_left (le_abs_self ρ) (mul_nonneg hτ hW)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hV hW) (abs_nonneg _))
  have split : Real.exp (-(2*κ)*(till x:ℝ)) = e*e := by
    dsimp only [e]; rw [←Real.exp_add]; congr 1; ring
  calc
    τ*(W*(ρ*Real.exp (-(2*κ)*(till x:ℝ)))) = (τ*W*ρ)*(e*e) := by rw [split]; ring
    _ ≤ (V*W*abs ρ)*(e*e) := mul_le_mul_of_nonneg_right hs (mul_nonneg he he)
    _ ≤ (V*W*abs ρ)*(e*(Real.exp 1 * B)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr he) hVW
    _ = ((V*W*abs ρ*Real.exp 1)*e)*B := by ring
    _ ≤ target*B := mul_le_mul_of_nonneg_right hpay (Real.exp_pos _).le

omit [Fintype I] in
/-- Prices for one physical occurrence with arbitrary cutoff and period, using the single table stored in the forecast. -/
theorem actual {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit) :
    let N := n j₁ j₀
    let r := p.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/4
    let c := min κ 1/100000
    let ρ := ManuscriptQLocalStoredGaussianScalar.cutAllowance G P₀ Pt N r
    let W := (max 1 (torusPay (PAC G 1) s))^N
    let C := W*(ρ*Real.exp (-(ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2)*(till θ:ℝ)))
    let D := g₀^(power j₁ j₀)*Real.exp (-c*(radiusB θ:ℝ))
    0<s ∧ 0<c ∧ C ≤ D ∧ torusPay PUnit.{1} s*C ≤ D := by
  intro N r s κ c ρ W C D
  have hs : 0<s := (ManuscriptQLocalScalarFields.priced.{0,0} R d p thermal).1
  have hκ : 0<κ := div_pos (ManuscriptQLocalScalarClockPurchase.cutoff_pos Pt (P₀).L) (by norm_num)
  have hc : 0<c := div_pos (lt_min hκ zero_lt_one) (by norm_num)
  have hW : 0≤W := pow_nonneg (zero_le_one.trans (le_max_left (1:ℝ) (torusPay (PAC G 1) s))) N
  let V := max 1 (torusPay PUnit.{1} s)
  have hp := ManuscriptQLocalScalarClockPurchase.demand_realized R (WilsonScalarSourceTableForecast.clock R p)
    d.cutoff d.level d.period d.below
  change abs (V*W*abs ρ*Real.exp 1) * Real.exp (-κ*(till θ:ℝ)) ≤ g₀^(power j₁ j₀) at hp
  have h2 : ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/2 = 2*κ := by dsimp only [κ]; ring
  refine ⟨hs,hc,?_,?_⟩
  · dsimp only [C]; rw [h2]
    simpa only [one_mul] using absorb hκ hW (show 0 ≤ (1:ℝ) by norm_num) (le_max_left _ _) hp
  · dsimp only [C]; rw [h2]
    exact absorb hκ hW (torusPay_nn PUnit.{1} s hs) (le_max_right _ _) hp

end YM.Integration.WilsonScalarSourceTableTariff
end

