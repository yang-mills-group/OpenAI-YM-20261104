import YM.Integration.WilsonOriginalCensusCanonicalInputs
import YM.Integration.WilsonReceivedCanonicalSocketReed

/-! The fixed finite selection of one submitted page per occupied original colour. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalFront
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
  {n:Side}(a:Fin (Pages n (fine R i per))→V→Lattice.Cover)
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


section SingleCopy
variable (a:V→Lattice.Cover)
local notation "roll" => start R d κ pt q a
local notation "ink" => WilsonOriginalCensusCanonicalInputs.inlet (h:=h) R d pt q N i per hi F a
local notation "signal" t:max => (WilsonReceivedDepositedVerseCensus.ordinary (roll) (present h) t).1 (f)

theorem submitted (s:Finset V):
    ∏j∈s,(ink) j=before R N i per hi F (signal s):=by
  change (∏j∈s,SignedMeasuredSourceSeries.probe (S) F (A) (ρ) (readO (present h) ((roll) {j}) (f)))=
    SignedMeasuredSourceSeries.probe (S) F (A) (ρ) (readO (present h) (levelsO (roll) s) (f))
  rw [WilsonReceivedCanonicalSocketLevels.canonical R d κ pt q a (present h) (f) s,map_prod]

theorem single_normalized (simple:G.Simple)(s:Finset V):
    Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ)*∏j∈s,(ink) j)=
      Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ))*
        flash (filed R N i per F (mass d s) (signal s)):=by
  rw [submitted (h:=h) R d pt q N i per hi F a s]
  have funded:Eu d (roll):=IndependentSourcePathFamily.legal _ a (fun j _=>grade R d κ pt j (q j))
  have material:Auth (mass d s) (WilsonReceivedDepositedVerseCensus.ordinary (roll) (present h) s):=
    (placedO (roll) funded s).tuft (touch (present h) s)
  exact WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple _ _
    (material.span (f)) (material.pale (f))

end SingleCopy

local notation "Ports" => Fin (Pages n (fine R i per))

def located {m:ℕ}(ports:Fin m→V→Lattice.Cover)(s:Finset V)(v:s→Fin m)(j:V):Lattice.Cover:=
  if hj:j∈s then ports (v ⟨j,hj⟩) j else 0

local notation "ink" => WilsonOriginalCensusCanonicalInputs.inlet (h:=h) R d pt q N i per hi F

theorem pin {a₁ a₂:V→Lattice.Cover}(j:V)(atSite:a₁ j=a₂ j):
    (ink) a₁ j=(ink) a₂ j:=by
  simp only [WilsonOriginalCensusCanonicalInputs.inlet,WilsonReceivedCanonicalVerseRegister.start,
    IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.single,atSite]

theorem positions (s:Finset V):
    (∏j∈s,∑p:Ports,(ink) (a p) j) = ∑v:s→Ports, ∏j∈s,(ink) (located a s v) j:=by
  classical
  calc
    _ = ∏j:s,∑p:Ports,(ink) (a p) j.val:= (prod_coe_sort s _).symm
    _ = ∑v:s→Ports,∏j:s,(ink) (a (v j)) j.val:=Fintype.prod_sum _
    _ = _:=by
      apply sum_congr rfl
      intro v _
      rw [←prod_coe_sort s]
      apply prod_congr rfl
      intro j _
      apply pin
      simp only [located,dif_pos j.property]

local notation "front" v:max => WilsonReceivedCanonicalVerseRegister.start R d (κ) pt q v
def normalized (s:Finset V):Ink (Woods G (coarse R i per)):=
  ∑v:s→Ports,flash (filed R N i per F (mass d s)
    ((WilsonReceivedDepositedVerseCensus.ordinary (front (located a s v)) (present h) s).1 (f)))

theorem original (simple:G.Simple)(s:Finset V):
    Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ)*∏j∈s,∑p:Ports,(ink) (a p) j)=
      Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ))*
        normalized (h:=h) (n:=n) R d pt q N i per F a s:=by
  rw [positions,normalized,Finset.mul_sum,Finset.mul_sum,W_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact single_normalized (h:=h) R d pt q N i per hi F tag (located a s v) simple s

end YM.Integration.WilsonOriginalCensusCanonicalFront
end
