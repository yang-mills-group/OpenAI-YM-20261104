import YM.Integration.WilsonReceivedDepositedOrbitalDatedGraph
import YM.Integration.WilsonOriginalCensusStagedCopies

/-! The original selected placements and the measured, separately submitted finite graph at each of them. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPlacements
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
variable {G:Gauge}{n:ℕ}{n':Side}{I:Type}[Fintype I]
  {P:Passport n' (Fin n)}(B:I→Binder P (Stock.census (Fin n))){D k:Fin n→ℕ}
  (old:Outerm G D)(q:ℕ)(root:I→Fin n)(y:Fin n→Lattice.Cover)(t:Case D)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n'.val∣(fine R i per).val)
local notation "ff" => fine R i per
local notation "load" => I×Fin (Pages n' (ff))
local notation "K₀" => model R N i per hi
local notation "vac" => relative R N i per hi F (covered R N i per)
local notation "held" u:max => (page h (B (u).1).center (u).2).val
local notation "field" u:max => offered old k q y t (B (u).1).mode.val (root (u).1) (ff) (held u)
local notation "before" u:max => WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F (field u)

open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalMixedGaussianTable (stock)
open WilsonReceivedDepositedOrbitalConditioned (staged)
open WilsonReceivedDepositedOrbitalRetained (income)
open private flat_constant from YM.Integration.WilsonReceivedCanonicalSocketWick
open private opening from YM.Integration.WilsonVacuumPreResetDepositedAction
variable (well:Wellness k old){σ cash:ℝ}(hs:0<σ)(fund:1≤cash)(book:CoverBill old q σ cash)
  (inside:∀u,root u∈(B u).mode.val)
local notation "Z₁" => I×Fin (Pages n' (ff))
local notation "J₁" => Stock.census (Z₁)
local notation "Q₁" => (K₀).covariance F tag
local notation "bank" => fun l:I=>offered old k q y t (B l).mode.val (root l)
local notation "mask" => fun l:I=>(B l).mode.val
local notation "massAt" => fun l:I=>mass k ((B l).mode.val)
local notation "picked" a:max => income (k:=k) B old q root y t R N i per F h a univ
variable (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room (Fin n)))
  (a:fieldDir G (coarse R i per) 1)
local notation "c₁" => fun u:(Z₁)=> ∏v∈(B u.1).mode.val,(x v).val
local notation "piece" => fun u:(Z₁)=>coefficient (J₁) (J₁).fire (c₁) u
local notation "amount" => fun s:Finset (Z₁)=>∏u∈s,(piece) u
local notation "V₀" => Wick (Woods G (coarse R i per)) (Q₁) (raiseE (vac))


open WilsonReceivedDepositedOrbitalMode (face)
variable (T:Finset (I×Fin (Pages n' (fine R i per))))

open WilsonReceivedDepositedOrbitalProper (retain)
open WilsonReceivedDepositedOrbitalKinetic (portrait)
open WilsonReceivedDepositedOrbitalGrade (booked)
local notation "L" => portrait (k:=k) B old q root y t R N i per F h T
local notation "deposit" => income (k:=k) B old q root y t R N i per F h T

open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalRawQReversion (coordinates dated)
open WilsonNeutralSignedPolynomialRate (read)
local notation "calendar" => ratioHigh (levels R) R.metals.O N i

open WilsonOriginalCensusCopyGraphs (graph)
open WilsonOriginalCensusCompatibleCopies (entry plate)
open WilsonOriginalCensusStagedCopies (pupil)
open WilsonReceivedDepositedAlias (fold)
open WilsonReceivedDepositedOrbitalPhases (name)
open WilsonReceivedDepositedOrbitalResponse (report)
open WilsonReceivedDepositedOrbitalSlice (hom)
open Extra.Trajectories (connected)
local notation "J₀" => Stock.census (Fin n)
local notation "Addr" => (u:Finset I) × (u→Fin (Pages n' (ff)))

def cut (s:Addr):Finset (Z₁):=graph s.1 s.2

def amountAt (target:(J₀).Mode)(s:Addr):ℂ:=
  entry (J₀) (pupil B) target s.1 (∏u:cut R i per s,(c₁) u.val)

def filing (A:Cost)(g:Addr):Ink (Woods G (coarse R i per)):=
  portrait (k:=k) B old q root y t R N i per F h (cut R i per g) A univ

private theorem selects {Z:Type}[DecidableEq Z](s:Finset Z):
    (Finset.univ:Finset s).map (Function.Embedding.subtype (·∈s))=s:=by
  ext v
  simp only [Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coe_subtype]
  exact ⟨fun ⟨v,eqn⟩=>eqn ▸ v.property,fun hv=>⟨⟨v,hv⟩,rfl⟩⟩

omit [Fintype I] in
private theorem bill_mul (target:(J₀).Mode)(s:Finset I)(a b:ℂ):
    entry (J₀) (pupil B) target s (a*b)=entry (J₀) (pupil B) target s a*b:=by
  unfold WilsonOriginalCensusCompatibleCopies.entry
  split
  · split <;> simp
  · simp

include well hs fund book inside hi tag in
theorem charged (simple:G.Simple)(r d:ℕ)(kept:d ≤ r)(target:(J₀).Mode):
    let K:=report (k:=k) B old q root y t R N i per F h x a r
    let rename:=fold (J₀) (name B R i per)
    (Order.observe (J₀) r (hom rename r (connected K)) d).part target=
      ∑g:Addr,amountAt B R i per x target g*
        (MvPolynomial.eval (flatten a) (coeff d (filing (k:=k) B old q root y t R N i per F h 1 g)):ℝ):=by
  intro K rename
  rw [WilsonReceivedDepositedOrbitalSlice.observe]
  have embossed:=WilsonOriginalCensusCompatibleCopies.original (J₀) (pupil B)
    (Order.observe (J₁) r (connected K) d) target
  rw [show (rename _).part target=_ from embossed,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  let placed:=graph u v
  have readout:=WilsonReceivedDepositedOrbitalProfile.heard B old q root y t R N i per hi F tag h well hs fund book inside x
    a placed simple r d kept univ
  have norm:=WilsonReceivedDepositedOrbitalResponse.normalized B old q root y t R N i per hi F tag h well hs fund book inside x a simple r
  dsimp only at readout
  rw [Order.logMarked,norm,retain,selects] at readout
  change entry (J₀) (pupil B) target u ((Order.observe (J₁) r (connected K) d).part (face placed))=_
  rw [readout,bill_mul]
  rfl

end YM.Integration.WilsonReceivedDepositedOrbitalPlacements
end
