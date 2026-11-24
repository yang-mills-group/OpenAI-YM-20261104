import YM.Integration.WilsonOriginalCensusCanonicalDigit
import YM.Integration.WilsonReceivedDepositedOrbitalFilteredStep

/-! A physical top socket at each occupied site only uses that site's actual
periodic image, even when its independent lifts on the cover differ. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalWrappedTrial
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
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Winding
open WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonReceivedCanonicalSocketSeed (contact present)
variable {G:Gauge}{V:Type} [Fintype V] [DecidableEq V] (R:Run G)(d:V→ℕ)
  {h:V→ℕ}(pt:V→Chamber)(q:(j:V)→Choice R d j)

theorem singleton (A:Case h)(n:Side)(a b:V→Lattice.Cover)(j:V)
    (agree:wrap n (a j)=wrap n (b j)):
    readO A (start R d (fun l=>contact (h l)) pt q a {j}) n =
      readO A (start R d (fun l=>contact (h l)) pt q b {j}) n:=by
  rw [WilsonReceivedCanonicalVerseChart.filed R d _ pt q a j,
    WilsonReceivedCanonicalVerseChart.filed R d _ pt q b j]
  simp only [readO,OriginalMarkedSourceComet.source,WilsonCoeffUV.Wheel.Mark.cn,
    WilsonCoeffUV.Mer.shifted,agree]

theorem marked (A:Case h)(n:Side)(a b:V→Lattice.Cover)(s:Finset V)
    (agree:∀j∈s,wrap n (a j)=wrap n (b j)):
    readO A (levelsO (start R d (fun l=>contact (h l)) pt q a) s) n =
      readO A (levelsO (start R d (fun l=>contact (h l)) pt q b) s) n:=by
  rw [WilsonReceivedCanonicalSocketLevels.canonical,WilsonReceivedCanonicalSocketLevels.canonical]
  exact prod_congr rfl (fun j hj=>singleton R d pt q A n a b j (agree j hj))

variable (N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
local notation "socket" a:max => start R d (fun l=>contact (h l)) pt q a

include hi tag in
theorem original (simple:G.Simple)(a b:V → Lattice.Cover)(s:Finset V)
    (agree:∀j∈s,wrap (fine R i per) (a j)=wrap (fine R i per) (b j)):
    WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i per F
        (ratioHigh (levels R) R.metals.O N i) a s =
      WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i per F
        (ratioHigh (levels R) R.metals.O N i) b s:=by
  have sold (z:V → Lattice.Cover):Eu d (socket z):=IndependentSourcePathFamily.legal _ z
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d (fun l=>contact (h l)) pt j (q j))
  have hush (z:V → Lattice.Cover):(socket z) ∅=0:=IndependentSourcePathFamily.empty _ z
  apply PowerSeries.ext
  intro u
  apply WilsonReceivedDepositedOrbitalFilteredStep.original R N i per hi F simple tag (u+1)
    (socket a) (socket b) (sold a) (sold b) (hush a) (hush b) (present h) s _ u (Nat.lt_succ_self u)
  intro v hv j hj
  change coeff j (SignedMeasuredSourceSeries.probe (step R i per) F (saddle R N i per F)
    (fderiv ℝ ((model R N i per hi).b F) 0)
    (readO (present h) (levelsO (socket a) v) (fine R i per))) = _
  rw [marked R d pt q (present h) (fine R i per) a b v (fun l hl=>agree l (hv hl))]
  rfl

end YM.Integration.WilsonIndependentCollarCanonicalWrappedTrial
end

