import YM.Integration.WilsonIndependentConditionedFolioCuts
import YM.Integration.WilsonIndependentSpoutHaarHistory
import YM.Integration.WilsonOriginalPublicNodalUnitHistory
import YM.Integration.WilsonIndependentConditionedFolioScalar

/-! The full live cutoff, native Ward grade, normalized Haar frame and scalar read on one origin. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioReporter
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open FormalBulk08.Series
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open WilsonReceivedFixedDigitFinite (computed)
open WilsonOriginalCensusUnitVerse (observed)
open scoped Classical BigOperators
open WilsonIndependentConditionedFolioReader (ear)
open WilsonOlderFreshHybridClock (flat)
open WilsonIndependentFittedPivotCash (measured)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonCoeffUV.Power PertExtension Metric Precision Exterior PowerSeries
open WilsonIndependentFittedMixedCash (embed)
variable {G:Gauge}(R:Run G)(u:G.ColorIndex)
local notation "L" => R.family.path.levels
variable (tags:∀ i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
variable (simple:G.Simple)(price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)

include u tags simple price funded in
theorem native (N K v a b:ℕ)(vk:v ≤ K)(kn:K ≤ N)(X:Era G ℝ)(ha:Auth a X)(hb:Auth b X):
    cruises L R.metals.O N a K v X=cruises L R.metals.O N b K v X:=by
  induction vk using Nat.decreasingInduction with
  | self=>rw [cruises_top,cruises_top]
  | of_succ i hi ih=>
    rw [cruises_sub L R.metals.O N a X hi,cruises_sub L R.metals.O N b X hi]
    have h':=cruising L simple R.alloy.B.ratio hi kn ha
    have h'':=cruising L simple R.alloy.B.ratio hi kn hb
    rw [ih] at h' ⊢
    exact WilsonOriginalPublicNodalUnitHistory.grades R u tags simple price funded N i a b (hi.trans_le kn) _ h' h''

include u tags simple price funded in
theorem reported {A:Levels G}{O:ChartRatio G}(levels:A=L)(reset:LocalRatio O)(N K v a b:ℕ)(vk:v ≤ K)(kn:K ≤ N)
    (X:Era G ℝ)(ha:Auth a X)(hb:Auth b X)(c:ℝ):
    cruises A O N a K v (c • X)=c • cruises L R.metals.O N b K v X:=by
  subst A
  rw [WilsonIndependentSpoutHaarHistory.original reset R.alloy.B.ratio L]
  rw [←native R u tags simple price funded N K v a b vk kn X ha hb]
  exact (cruiseT (c • ContinuousLinearMap.id ℝ ℝ) L vk simple R.alloy.B.ratio kn ha).symm

theorem scalar (q:ℕ)(g:ℝ)(z:Fin 0→YForest G)(X:Era G ℝ)(c:ℝ):
    ear q g z (c • X)=((c * flat X q g :ℝ):ℂ):=by
  have zi:z=Fin.elim0:=Subsingleton.elim _ _
  subst z
  change cash q g (embed (WilsonOlderFreshSoftSocketKinetic.reading (c • X).2 Fin.elim0))=_
  simp only [cash,embed,WilsonOlderFreshSoftSocketKinetic.reading,flat,WilsonOlderFreshTerminalProgramme.series,Finset.mul_sum,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,PowerSeries.coeff_map,PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro i _
  change (g:ℂ)^i * ((c * X.2 i 0 Fin.elim0 :ℝ):ℂ)=_
  push_cast
  ring

end YM.Integration.WilsonIndependentConditionedFolioReporter
end
