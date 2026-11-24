import YM.Integration.WilsonReceivedDepositedOrbitalPortraitDegree
import YM.Integration.WilsonReceivedDepositedOrbitalPlacements
import YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels

/-! The angular degree of an occupied print depends on its inherited block names, uniformly in the number of actual auxiliary pages. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalGraphDegree
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
open WilsonReceivedCanonicalSocketChannels
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel.Mark

open WilsonReceivedCanonicalSocketSeed
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered)
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic.Near

open WilsonOriginalThreeCopiedCharts WilsonOriginalMixedBlockRows WilsonOlderFreshGraphSlate
open WilsonOriginalCensusCopySlate WilsonReceivedDepositedOrbitalFixedMoments
open WilsonVacuumPreResetDepositedLetters WilsonCoeffUV.Bank.Mosaic
variable {G:Gauge}{n:ℕ}{n':Side}{I:Type}
  {P:Passport n' (Fin n)}(B:I→Binder P (Stock.census (Fin n))){D k:Fin n→ℕ}
  (old:Outerm G D)(q:ℕ)(root:I→Fin n)(y:Fin n→Lattice.Cover)(t:Case D)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n'.val∣(fine R i per).val)
local notation "ff" => fine R i per
local notation "load" => I×Fin (Pages n' (ff))

open WilsonReceivedDepositedOrbitalRetained (family roots paid)
open WilsonReceivedDepositedOrbitalFixedLabels (name whole)
open WilsonReceivedDepositedOrbitalPlacements (cut filing)
open WilsonOriginalCensusCopyGraphs (graph)
open WilsonNeutralSignedPolynomialRate (read)
open WilsonOriginalRawQReversion (coordinates)
open Comparison.RG02.Valence WilsonCoeffUV.Bank.Mosaic
variable [Fintype I]
def width (k:Fin n→ℕ):ℕ:=∑u:I,mass k ((B u).mode.val)

theorem portion (S:Finset I)(pg:S→Fin (Pages n' (ff))):
    mass (fun u:graph S pg=>mass k (B u.val.1).mode.val) univ≤width B k:=by
  have paid:(∑u:graph S pg,mass k (B u.val.1).mode.val)=∑u∈S,mass k (B u).mode.val:=by
    conv_rhs => rw [←whole S pg,sum_map]
    rfl
  exact paid.le.trans (Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _))

variable (well:Wellness k old){σ cash:ℝ}(hs:0<σ)(fund:1≤cash)(book:CoverBill old q σ cash)
  (inside:∀u,root u∈(B u).mode.val)
include hi well hs fund book inside in
theorem original (simple:G.Simple)(S:Finset I)(pg:S→Fin (Pages n' (ff)))(d:ℕ):
    Level ((width B k+d:ℕ):ℤ) (fun b=>read (coordinates G (coarse R i per))
      (filing (k:=k) B old q root y t R N i per (repeatF (step R i per)) h 1 ⟨S,pg⟩) d b):=by
  let A:=graph S pg
  let degrees (u:A):=mass k (B u.val.1).mode.val
  let rooms:=family (k:=k) B old q root y t R i per A
  let place:=roots B R i per h A
  let M:=rooms place
  have earning:Eu degrees M:=(paid B old q root y t R i per A well hs fund book inside).1.level' place
  have degree:=WilsonReceivedDepositedOrbitalPortraitDegree.original R N i per hi degrees (@reading A)
    simple M earning 1 univ d
  have cap:mass degrees univ+d≤width B k+d:=Nat.add_le_add_right (portion (k:=k) B R i per S pg) d
  dsimp only [WilsonReceivedDepositedOrbitalPlacements.filing,WilsonReceivedDepositedOrbitalPlacements.cut,
    WilsonReceivedDepositedOrbitalKinetic.portrait,WilsonVacuumPreResetStationaryChange.ratio]
  dsimp only [degrees,rooms,place,M,A] at degree
  have projected:=degree.promote (Int.ofNat_le.mpr cap)
  exact projected

end YM.Integration.WilsonReceivedDepositedOrbitalGraphDegree
end
