import YM.Integration.WilsonScalarSourceTableDirections
import YM.Integration.WilsonScalarSourceTableTariff

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonScalarSourceTableDecay
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

private theorem raiseCost {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {N : ℕ} {f : X → ℝ} {C D : ℝ}
    (H : Through N f 0 C) (bound : C ≤ D) : Through N f 0 D :=
  ⟨H.smooth, fun j hj => (H.pay j hj).trans bound⟩

/-- One original stage forecast gives unit coefficients, arbitrary coupling order, and both original spatial exponents. -/
theorem original {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit)
    (ideal : ManuscriptQLocalIdealSquare.Paid n R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀) :
    let N := n j₁ j₀
    let r := p.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/4
    let c := min κ 1/100000
    let C := g₀^(power j₁ j₀)*Real.exp (-c*(radiusB θ:ℝ))
    let K := C*Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ Through N (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through N (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through N (ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o) 0 C ∧
    Through N (fun B => ManuscriptQLocalScalarDirections.error R d k U.val q a Z o B -
      ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o B) 0 K := by
  intro N r s κ c C K
  obtain ⟨hs,hc,H,J⟩ := WilsonScalarSourceTableTariff.actual R d p thermal
  obtain ⟨_,_,reg,changed,store,storeChanged⟩ := ManuscriptQLocalScalarDirections.pricedFixed R d p thermal ideal k q a z U Y Z o
  have spatial := mul_le_mul_of_nonneg_right J (Real.exp_pos (-s*(separation o z:ℝ))).le
  exact ⟨hs,hc,raiseCost reg H,raiseCost changed spatial,raiseCost store H,raiseCost storeChanged spatial⟩

/-- The same chosen kit also meets the original stored scalar purchase. -/
theorem stored {n power : ℕ→ℕ→ℕ} (p : WilsonScalarSourceTableForecast.Paid n power R.kit)
    (thermal : ManuscriptQLocalScalarClockPurchase.Paid n R.kit) (ideal : ManuscriptQLocalIdealSquare.Paid n R.kit) :
    ManuscriptQLocalStoredGaussianScalar.Paid n R.kit := ⟨ideal,WilsonScalarSourceTableForecast.source R p,thermal⟩

def Program (G : Gauge) (n power : ℕ → ℕ → ℕ) : Prediction G :=
  @FundedPredictionSupply.Both G (@WilsonScalarSourceTableForecast.Paid G n power)
    (@FundedPredictionSupply.Both G (@ManuscriptQLocalScalarClockPurchase.Paid G n) (@ManuscriptQLocalIdealSquare.Paid G n))

theorem program_prices (G : Gauge) (n power : ℕ → ℕ → ℕ) : FundedPredictionSupply.AllPrices (@Program G n power) :=
  fun s K => FundedPredictionSupply.both (WilsonScalarSourceTableForecast.prices n power s K)
    (FundedPredictionSupply.both (ManuscriptQLocalScalarClockPurchase.allPrices n s K) (ManuscriptQLocalIdealSquare.prices n s K))

end YM.Integration.WilsonScalarSourceTableDecay
end

