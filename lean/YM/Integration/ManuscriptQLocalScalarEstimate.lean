import YM.Integration.ManuscriptQLocalScalarClockPurchase

/-! Complete scalar part of the manuscript local comparison at the true
physical fine coupling, after all requested source and cutoff purchases. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarEstimate
open Marker Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonLimitConstruction PhysicalAffineScalarClockCost ConditionalCovarianceCutoff
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L
local notation "a₀" => (Pt).top.paths
local notation "b₀" => (Pt).top.width
local notation "β₀" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "g₀" => coupling β₀

omit [Fintype I] in
/-- Two genuine no-hole root prices, regular and one changed tree, with all
external independent coarse components. The coefficient is a purely
geometric stage number; the original fine temperature has been absorbed
by its prospective clock receipt at the same cutoff. -/
theorem original {order : ℕ→ℕ→ℕ} (paid : FundedPredictionSupply.Both
    (@ManuscriptQLocalScalarSourcePurchase.Paid G order) (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit) :
    let n := order (j₁) (j₀)
    let r := paid.1.choose (j₁) (j₀)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) (S).patch.L
    let w := width G (S).patch (S).kernel (T).high (n+1) a₀ b₀
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G (S).patch (S).kernel (T).high (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) (S).patch.L n
    0<δ ∧ 0<M ∧ 0 < min δ w ∧ 0<κ/2 ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ)
    (tag : Site c₀) (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
    let fee := allowance G (S).patch (S).kernel (T).high n a₀ b₀ δ r.ordinary r.discarded M
    ((marks G c₀ (min δ w)).pay l o * |jet (ray G c₀) (ManuscriptQLocalCompleteScalar.regular R d k q b Y g₀ o) l 0| ≤
      fee*Real.exp (-(κ/2)*(till θ:ℝ))) ∧
    ((marks G c₀ (min δ w)).pay l o * ((native c₀).weight (min δ w) o tag *
      |jet (ray G c₀) (ManuscriptQLocalCompleteScalar.error R d k q b tag F' Y Z g₀ o) l 0|) ≤
      fee*Real.exp (-(κ/2)*(till θ:ℝ))) := by
  intro n r κ w δ M
  have hHot := ManuscriptQLocalScalarClockPurchase.realized R paid.2 d.cutoff d.level d.period d.below
  have hBand := ManuscriptQLocalScalarClockPurchase.band R d.cutoff d.level d.period d.below
  obtain ⟨hδ,hM,hτ,hκ,h⟩ := ManuscriptQLocalCompleteScalar.original R d paid.1
  have hρ := ConditionalAffineSourcePrices.rate_pos (Pt) (S).patch.L
  have hLg : 0≤ManuscriptQLocalCompleteScalar.logFee G (S).patch (S).kernel (T).high n a₀ b₀ :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (cut_nonneg (Pt).top.width_pos (Pt).top.paths_pos.le (by norm_num : 0≤(0:ℝ)) 0) (by norm_num))
  have acquired := PhysicalAffineScalarClockCost.priced G (S).patch (S).kernel (T).high n a₀ b₀ δ
    r.ordinary r.discarded M ρ κ θ β₀ hδ r.ordinary_pos.le r.discarded_pos.le hM.le hρ.le hLg hBand.1 hBand.2 hHot
  refine ⟨hδ,hM,hτ,half_pos hκ,?_⟩
  intro k q b tag F' Y Z o l hl fee
  have step := h k q b tag F' Y Z g₀ o l hl
  exact ⟨step.2.trans acquired,step.1.trans acquired⟩

end YM.Integration.ManuscriptQLocalScalarEstimate

