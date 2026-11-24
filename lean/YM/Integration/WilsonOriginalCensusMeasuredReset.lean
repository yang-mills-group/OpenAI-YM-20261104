import YM.Integration.WilsonOriginalCensusGaussianCopies

/-! The high operand of the original two-print comparison is evaluated with
its measured kinetic reversion after the full deposited Gaussian return. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusMeasuredReset
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

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
open QuadraticLocal.Rebirth FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  (pieces : V → Submodule ℝ ℂ) (grades : V → ℕ) (order shelf seats : ℕ)
  (physical : Wallet (room V) → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (room V) pieces grades
    order shelf seats i hi physical)
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead (room V)
  P.model order P.voter
local notation "starts" => Oak.grade0 R hk D Q π Γ hi P.lesson
local notation "stamped" => Mutation.stamp student (Γ i) starts (Burn.horizon k+2) order

variable {I:Type}[Fintype I]{port:Passport (R.family.side (i+1) per) V}
  (B:I → Binder port (Stock.census V)){q:ℕ}{σ:ℝ}
  (T:∀l,Copy G (∑v∈(B l).mode.val,grades v) q σ)
  (Z:I → (n:Side) → Site n → PChart G n)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (B (l)).center) disk
local notation "M" => mounted B (fun l=>own l)

include course in
theorem original (placed:P.passport=port)(names:P.modelIndex=((l:I)×(T l).Roster))(ink:HEq P.model M)
    {w:V → ℝ}{σ₀ C:ℝ}{p₀ seats₀ shelf₀:ℕ}
    (stock:Scene.Armada P.model w grades σ₀ C p₀ seats₀ shelf₀)(width:0 < σ₀)(hs:0 < σ)
    (shell:∀l n y,shellK (∑v∈(B l).mode.val,grades v) (Z l n y))
    (pure:∀l n y a,Pure (Z l n y a))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    (pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    {quiet:ℕ → SeriesA G}(actual:Read R N m (Burn.horizon k) quiet π Γ){τ cash:ℝ}
    (funded:Issued R N (i+1) (Burn.horizon k) (quiet (i+1)) τ cash)
    (legal:Legal tape (π (i+1)))(fits:order ≤ Burn.horizon k+1)(rank:order ≤ q)(narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (x:Affinity.Wallet (room V))(grid:Side)(tiles:(R.family.side i per).val∣grid.val)
    (trees:∀b:Covers R.family.path.levels.S i grid,Forest (step R i b.val).ratio)
    (tags:∀b:Covers R.family.path.levels.S i grid,(step R i b.val).Choices)
    (r:ℕ)(through:r ≤ order)(s:Hot (Stock.census V))(e:ℕ)(kept:e ≤ r)(Y:Stationary.Link G grid):
    (peek tiles stamped grades (π i) tape x e Y).part s.val=
    Adjacent.born (fun a z=>(WilsonOriginalCensusGaussianCopies.value R cut B Z x grid tiles trees tags order z a).part s.val)
       ((Rebirth.caliber (Γ i) starts).back (Burn.horizon k+2)) 0 r e Y:=by
  apply WilsonOriginalRetainedStamp.original (R:=R) (hk:=hk) (course:=course) (cut:=cut)
    (pass:=pass) (month:=month) (fits:=fits) (narrow:=narrow) (issued:=P.issued.earning)
    (x:=x) (h:=tiles) (small:=through) (kept:=kept) (s:=s) (z:=Y)
  intro a included z
  have ownread:=WilsonOriginalCensusSelectedCopy.entered R hk D Q π Γ Ψ course books hi cut ahead (room V)
    pieces grades order shelf seats physical P x grid tiles trees tags a (included.trans through) z
  have sourced:=WilsonOriginalCensusGaussianCopies.filed R cut B Z x grid tiles trees tags grades T
    P.model placed names ink stock width hs shell pure matched legal actual hi funded order rank (by omega) z a
  exact sourced.symm.trans ownread

end YM.Integration.WilsonOriginalCensusMeasuredReset
end
