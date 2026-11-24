import YM.Integration.WilsonIndependentMatchedOpeningPorts
import YM.Integration.WilsonIndependentMatchedOpeningComposite
/-! Expand the actually issued old-vacuum K product on genuine visited nodes, keeping each summand's true angular ceiling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningTarget
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedOpeningPorts (Port submitted)
open WilsonIndependentMatchedOpeningCensus (pace Sites top entry)
open WilsonIndependentMatchedOpeningComposite (branch keys weight)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedOpeningRoster (field)
open RegulatorIR.Cluster
variable {G:Gauge}{H:Hol G}{n h D k u e:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (s:Fin (n+1)→Bool)(d:Fin (n+1)→ℕ)(cut:∀i,d i<D)
    (c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(φ:Fin (n+1)→Rarity D)
    (y:ℝ)(o:Fin (n+1)→ CellR)(a:Fin (n+1)→ℝ)
    (X:Fin (n+1)→CutsP H T p v E A K U)(amp:Fin (n+1)→ℝ)

theorem original {L:Torch H T p v E A K}{run:XSpace.Run}{base idx f:ℕ}
    {δ η:ℝ}{fee:Fin (n+1)→ℝ}
    (file:∀i,Filed (X i) L run base idx f (amp i) δ η (fee i)
      (Shrine (plate (sectionAt R W (s i) (d i)) (cut i)) (c i))):
    MassP G ℝ n (top φ y o a X amp)=
      ∑z:((i:Fin (n+1))→Sites R d φ y o X i),
        affiled (∏i,weight R d cut c φ y o a X z i)
          (field R W s d (keys R d φ y o X z) (D:=fun _=>D) cut
            (WilsonIndependentMatchedOpeningComposite.points R d φ y o X z) (branch n id)):=by
  rw [(WilsonIndependentMatchedOpeningCensus.original R W s d cut c φ y o a X amp file).1]
  exact Finset.sum_congr rfl fun z _=>WilsonIndependentMatchedOpeningComposite.original R W s d cut c φ y o a X z
end YM.Integration.WilsonIndependentMatchedOpeningTarget
