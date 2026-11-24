import YM.Integration.WilsonReceivedDepositedOrbitalRetained
import YM.Integration.WilsonReceivedDepositedOrbitalConditioned
import YM.Integration.WilsonReceivedCanonicalSocketMoments

/-! All finite Wick moments of the true deposited source are read from independently
affordable subfamilies of the genuine rooted pages. The scalar vacuum is removed once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalResponse
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

def report (r:ℕ):Grade (J₁) r:=
  stock (J₁) r (flatten a) (amount) (fun S=>picked S)

include well hs fund book inside in
theorem phase (l:I)(u:Site (ff)):
    shellK (mass k ((B l).mode.val)) ((bank) l (ff) u) ∧
      ∀j,Pure (((bank) l (ff) u) j):=by
  let z:I→Lattice.Cover:=fun _=>Lattice.lift u
  let bank₀:=program (k:=k) old q (mask) root (fun _:I=>y) (fun _:I=>t)
  have paid:=WilsonReceivedDepositedOrbitalFixedMoments.authentic old q (mask) root (fun _:I=>y) (fun _:I=>t)
    well hs fund book inside
  have sub:=((paid.1.level' z {l}).tuft (touch reading {l}))
  have price:Auth (mass k ((B l).mode.val)) (tuftV (touch reading {l}) (bank₀ z {l})):=by
    simpa only [mass,Finset.sum_singleton] using sub
  have word:((tuftV (touch reading {l}) (bank₀ z {l})).1 (ff))=(bank) l (ff) u:=by
    change pPly reading {l} ((bank₀ z {l}).1 (ff))=_
    simpa only [z,wrap_lift] using
      (socket old q (mask) root (fun _:I=>y) (fun _:I=>t) R i per z l)
  exact word ▸ ⟨price.span (ff),price.pale (ff)⟩

include well hs fund book inside in
theorem raw (simple:G.Simple)(r:ℕ):
    staged B R N i per hi F tag h x (bank) a r=
      stock (J₁) r (flatten a) (amount) (fun S=>(V₀)*(picked S)):=by
  rw [WilsonReceivedDepositedOrbitalWick.original B R N i per hi F tag h x (bank) a r]
  unfold WilsonReceivedDepositedOrbitalWick.filed
  apply congrArg (stock (J₁) r (flatten a) (amount))
  funext S
  exact WilsonReceivedDepositedOrbitalRetained.whole B old q root y t R N i per hi F tag h S
    well hs fund book inside simple

include well hs fund book inside in
theorem normalized (simple:G.Simple)(r:ℕ):
    Order.ratio (staged B R N i per hi F tag h x (bank) a r)=
      report (k:=k) B old q root y t R N i per F h x a r:=by
  rw [raw B old q root y t R N i per hi F tag h well hs fund book inside x a simple r]
  have head:constantCoeff (V₀)=1:=opening _ _ (flat_constant R N i per hi F)
  have nz:(V₀)≠0:=by
    intro erased
    rw [erased,map_zero] at head
    exact zero_ne_one head
  apply WilsonReceivedDepositedOrdinaryFactor.cancel _ _ _ (piece) (fun s=>picked s) (V₀) head
  · apply mul_left_cancel₀ nz
    rw [mul_one]
    have blank:=WilsonReceivedDepositedOrbitalRetained.whole B old q root y t R N i per hi F tag h
      (∅:Finset (Z₁)) well hs fund book inside simple
    simpa only [Finset.prod_empty,mul_one] using blank.symm
  · intro j
    have ne:(J₁).quiet≠(J₁).fire j:=Ne.symm ((hot_iff_ne _).mp ⟨j,Finset.mem_singleton_self j⟩)
    simp [WilsonCapturedPrimaryWindingVerseRoster.coefficient,Poly.part_smul,Poly.part_send,ne]

end YM.Integration.WilsonReceivedDepositedOrbitalResponse
end
