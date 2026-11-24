import YM.Integration.WilsonOlderFreshLocatedFaculty
import YM.Integration.WilsonOlderFreshPointNamedCubic
import YM.Integration.WilsonOlderFreshPointFiledEdge
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshThermometerSlots
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology


open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
open WilsonMeasuredJointCensusCash
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
open WilsonOlderFreshPointRegistry

open WilsonOlderFreshGraphCommonHouse WilsonOlderFreshGraphSchool WilsonOlderFreshGraphAllStages
open WilsonLimitConstruction WilsonWindowBookPurchase WilsonWindowUniversalSchool
open QuadraticLocal.Advent.Sycamore WilsonLimitConstruction.FundedCompanySelection WilsonMeasuredPointHouseSeats
universe u
variable {G:Gauge}
local notation "families" R:max => (fun i:ℕ=>Flat.routes ((R:Run G).family.path.levels.clock.op i 0).patch)
local notation "M" => WilsonOlderFreshGraphAllStages.menu G
local notation "H" h:max R:max => WilsonOlderFreshGraphSchool.roots M h (R:Run G).metals.p (R:Run G).metals.K
local notation "tab" h:max R:max => WilsonOlderFreshGraphSchool.rollTab M h (R:Run G).metals (R:Run G).rolls

def request (Q:ℕ):Fin 3 → WilsonOlderFreshGraphAllStages.Query:=
  Fin.cases (WilsonOlderFreshPointNamedCubic.reporter Q) fun _=>WilsonOlderFreshPointFiledEdge.reporter Q

theorem dimension (Q:ℕ)(w:Fin 3):(request Q w).letter.toll=WilsonOriginalThermometerPalette.levels w:=by
  fin_cases w <;> rfl

def horizon (Q q:ℕ):=WilsonMeasuredPointHouseSeats.order Q q+q+18

def semester (Q q:ℕ):Syl.School (horizon Q q):=
  ⟨WilsonMeasuredPointHouseSeats.order Q q,3,14,by unfold horizon Burn.horizon;omega,
    by unfold horizon Burn.horizon;omega,by unfold horizon Burn.horizon;omega⟩

def cut (q:ℕ):=3*(2*4+7+1+(q+3))

theorem launch (Q q:ℕ):
    (semester Q q).pieces=3 ∧ (semester Q q).horizon=14 ∧ Q ≤ (semester Q q).order ∧
    (semester Q q).order+14 ≤ Burn.horizon (horizon Q q)+2:=by
  refine ⟨rfl,rfl,?_,?_⟩
  all_goals dsimp [semester,horizon,WilsonMeasuredPointHouseSeats.order,Burn.horizon];omega

theorem original (R:Run G)(simple:G.Simple){φ:ℕ → ℕ}(scroll:VowsR.LawScroll G φ)(a:hue G)
    (funded:WilsonOlderFreshLocatedFaculty.Elected R simple scroll a)
    (Q q:ℕ)(order:cut q ≤ Q)(dmax:Fin 3 → ℕ)(depth:∀w,(request Q w).letter.toll<dmax w)
    (loc:Loc G 1)(ε:ℝ)(ep:0<ε):
    WilsonOlderFreshLocatedSharedRoom.Filed R (H simple R) (tab simple R) (φ:=φ)
      (request Q) dmax depth a (semester Q q) q ε:=by
  obtain ⟨_,_,_,slate⟩:=funded
  apply slate 3 (request Q) dmax depth loc (semester Q q) q ε ep
  · dsimp [semester,WilsonMeasuredPointHouseSeats.order];omega
  · dsimp [horizon,WilsonMeasuredPointHouseSeats.order];omega
  · norm_num [semester]
  · dsimp [Burn.horizon,horizon,WilsonMeasuredPointHouseSeats.order];omega
  · intro w;fin_cases w <;> first | exact (by decide : 6 ≤ 14) | exact (by decide : 4 ≤ 14)
  · intro w;fin_cases w <;> exact (launch Q q).2.2.1
  · intro w
    have four:3*(2*4+(4+1)+1+(q+3)) ≤ Q:=by unfold cut at order;omega
    fin_cases w <;> first | exact order | exact four

end YM.Integration.WilsonOlderFreshThermometerSlots
end
