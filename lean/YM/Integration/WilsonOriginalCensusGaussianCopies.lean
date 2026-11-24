import YM.Integration.WilsonOriginalCensusGaussianTable
import YM.Integration.WilsonOriginalCensusSelectedCopy

/-! Each genuine auxiliary page is normalized once, after its entire dated
Gaussian table has been evaluated on the same forest and physical quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusGaussianCopies
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Filter AllOrder.Floe Comparison.RG02 FVA1Physical.TwoReset
open WilsonOriginalCopiedContraction
open scoped Topology
variable {G:Gauge}(R:Run G){j N per:ℕ}(hi:j < N){V I:Type}[DecidableEq V][Fintype V][Fintype I]
  {P:Passport (R.family.side (j+1) per) V}(B:I → Binder P (Stock.census V))
  (Z:I → (n:Side) → Site n → PChart G n)(x:Affinity.Wallet (room V))
  (grid:Side)(tiles:(R.family.side j per).val∣grid.val)
  (trees:∀b:Covers R.family.path.levels.S j grid,Forest (step R j b.val).ratio)
  (tags:∀b:Covers R.family.path.levels.S j grid,(step R j b.val).Choices)
local notation "J" => Stock.census V

def page (r:ℕ)(b₀:Stationary.Link G grid)(d:ℕ)(c:Covers R.family.path.levels.S j grid):Poly (J):=
  let b:=AllOrder.Ker.convey (coverWin c.prop) b₀
  let A:=Stationary.arm G _ 1 b
  let Q₀:=(model R N j c.val hi).covariance (trees c) (tags c)
  let H:=fun z=>WilsonOriginalCensusPaidForest.value B R N j c.val hi (trees c) (tiled R tiles c) x Z A z r
  let table₀:=WilsonOriginalGaussianPaidTable.table (Board (J) r) Q₀ H
  (((Pages grid (R.family.side j c.val):ℕ):ℝ)⁻¹ :ℝ) • Order.observe (J) r (Order.logMarked table₀) d

def value (r:ℕ)(b:Stationary.Link G grid)(d:ℕ):Poly (J):=
  limUnder (coverFilter R.family.path.levels.S j grid) (page R hi B Z x grid tiles trees tags r b d)

variable (grades:V → ℕ){q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(B l).mode.val,grades v) q σ)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (B (l)).center) disk
local notation "M" => mounted B (fun l=>own l)
theorem filed {p':Passport (R.family.side (j+1) per) V}{μ:Type}
    (high:μ → Row p' (J) G (Affinity.Wallet (room V)))
    (placed:p'=P)(names:μ=((l:I)×(T l).Roster))(ink:HEq high M)
    {w:V → ℝ}{σ₀ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada high w grades σ₀ C order seats shelf)(width:0 < σ₀)(hs:0 < σ)
    (shell:∀l m y,shellK (∑v∈(B l).mode.val,grades v) (Z l m y))
    (pure:∀l m y a,Pure (Z l m y a))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    {start e:ℕ}{quiet:ℕ → SeriesA G}{π:ℕ → Layout G}{Γ:ℕ → Pace.Coin}
    (legal:Legal (Step.tape (e+2)) (π (j+1)))
    (course:Read R N start e quiet π Γ)(live:start ≤ j){τ cash:ℝ}
    (funded:Issued R N (j+1) e (quiet (j+1)) τ cash)
    (r:ℕ)(through:r ≤ q)(grade:r ≤ e+2)(b₀:Stationary.Link G grid)(d:ℕ):
    WilsonOriginalCoverCoefficient.read R hi r grid
      (fun c=>copyColor (tiled R tiles c) high grades (fun a=>(high a).paint x) (π (j+1)) (Step.tape (e+2)))
      trees tags d b₀=value R hi B Z x grid tiles trees tags r b₀ d:=by
  subst p' μ
  cases eq_of_heq ink
  unfold value WilsonOriginalCoverCoefficient.read
  apply congrArg (limUnder (coverFilter R.family.path.levels.S j grid))
  funext c
  let b:=AllOrder.Ker.convey (coverWin c.prop) b₀
  have paid:=WilsonOriginalCensusGaussianTable.original B grades T R N j c.val hi (trees c) (tags c) (tiled R tiles c)
    x (π (j+1)) (Step.tape (e+2)) Z stock width hs legal shell pure matched course live funded b r through grade
  exact congrArg (fun v=>(((Pages grid (R.family.side j c.val):ℕ):ℝ)⁻¹ :ℝ) • Order.observe (J) r v d) paid.2.1

end YM.Integration.WilsonOriginalCensusGaussianCopies
end
