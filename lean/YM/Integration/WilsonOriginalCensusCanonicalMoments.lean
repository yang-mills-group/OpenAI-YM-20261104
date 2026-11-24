import YM.Integration.WilsonOriginalCensusCanonicalWick
import YM.Integration.WilsonOriginalCensusCanonicalFront
import YM.Integration.WilsonReceivedDepositedOrdinaryFactor
import YM.Integration.WilsonReceivedFixedDigitCanonical

/-! Ordinary stocks on the original copy board after its one actual quiet division. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalMoments
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] (R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room V)){n:Side}(a:Fin (Pages n (fine R i per))→V→Lattice.Cover)
local notation "J" => Stock.census V
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "φ" => relative R N i per hi F (covered R N i per)
local notation "badge" => (fun j:V=>(J).fire j)
local notation "c" => (fun j:V=>(x j).val)

open WilsonVacuumPreResetStationaryChange WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis

open WilsonOriginalMixedGaussianTable (stock)


open WilsonOriginalCensusCanonicalWick (flat_constant)
open private opening from YM.Integration.WilsonVacuumPreResetDepositedAction


local notation "W₀" => Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ))
local notation "terms" => WilsonOriginalCensusCanonicalFront.normalized (h:=h) (n:=n) R d pt q N i per F a
local notation "bill" => WilsonOriginalCensusCanonicalWick.printed (h:=h) (n:=n) R d pt q N i per hi F tag x a

def moments (B:fieldDir G (coarse R i per) 1)(r:ℕ):Grade (J) r:=
  stock (J) r (flatten B) (fun s:Finset V=>∏j∈s,coefficient (J) badge (c) j) (terms)

private theorem quiet (j:V):(coefficient (J) badge (c) j).part (J).quiet=0:=by
  have nq:(J).quiet≠(J).fire j:=by
    intro eqn
    have hcard:=congrArg (fun s:(J).Mode=>s.val.card) eqn
    simp [Census.fire,Census.quiet] at hcard
  simp [WilsonCapturedPrimaryWindingVerseRoster.coefficient,Poly.part_smul,Poly.part_send,nq]

include hi tag in
theorem empty (simple:G.Simple):(terms) ∅=1:=by
  have head:constantCoeff (W₀)=1:=opening _ _ (flat_constant R N i per hi F)
  have nonzero:(W₀)≠0:=by
    intro hz
    rw [hz,map_zero] at head
    exact zero_ne_one head
  have base:=WilsonOriginalCensusCanonicalFront.original (h:=h) (n:=n) R d pt q N i per hi F tag a simple ∅
  simp only [Finset.prod_empty,mul_one] at base
  apply mul_left_cancel₀ nonzero
  rw [mul_one]
  exact base.symm

theorem original (simple:G.Simple)(B:fieldDir G (coarse R i per) 1)(r:ℕ):
    Order.ratio ((bill) B r)=moments (h:=h) (n:=n) R d pt q N i per F x a B r:=by
  unfold WilsonOriginalCensusCanonicalWick.printed WilsonOriginalCensusCanonicalWick.inlet
  simp_rw [WilsonOriginalCensusCanonicalFront.original (h:=h) (n:=n) R d pt q N i per hi F tag a simple]
  exact WilsonReceivedDepositedOrdinaryFactor.cancel (J) r _ _ _ (W₀)
    (opening _ _ (flat_constant R N i per hi F)) (empty (h:=h) (n:=n) R d pt q N i per hi F tag a simple) (quiet x)

/-- At the actual planting date the all-face inputs are exactly the fixed-child
canonical seeds, independently for every deck address of every occupied slot. -/
theorem planted (cells:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels V)
    (s:Finset V):
    (terms) s = ∑v:s→Fin (Pages n (fine R i per)),
      flash (filed R N i per F (mass d s)
        ((WilsonReceivedDepositedVerseCensus.ordinary
          (WilsonReceivedFixedDigitCanonical.fixed R d (κ) pt N (i+1) (i+1) cells q
            (WilsonOriginalCensusCanonicalFront.located a s v))
          (present h) s).1 (f))) := by
  simp only [WilsonReceivedFixedDigitCanonical.fixed, Nat.sub_self,
    WilsonReceivedFixedDigitHistory.itinerary, WilsonOriginalCensusCanonicalFront.normalized]

end YM.Integration.WilsonOriginalCensusCanonicalMoments
