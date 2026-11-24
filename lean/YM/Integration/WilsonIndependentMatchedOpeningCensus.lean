import YM.Integration.WilsonIndependentMatchedOpeningPorts
import YM.Integration.WilsonIndependentMatchedOpeningMass
/-! Expand the actually issued old-vacuum K product on genuine visited nodes, keeping each summand's true angular ceiling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningCensus
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
variable {G:Gauge}{H:Hol G}{n h D k u e:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (s:Fin (n+1)→Bool)(d:Fin (n+1)→ℕ)(cut:∀i,d i<D)
    (c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(φ:Fin (n+1)→Rarity D)
    (y:ℝ)(o:Fin (n+1)→ CellR)(a:Fin (n+1)→ℝ)
    (X:Fin (n+1)→CutsP H T p v E A K U)(amp:Fin (n+1)→ℝ)

def pace (i:Fin (n+1)):ℝ:=paceT (X i).ax.S (X i).m ((X i).m+(X i).i)
abbrev Sites (i:Fin (n+1)):=Port (R.family.labels.level (d i)) (φ i) (pace X i) y (o i)
def entry (i:Fin (n+1))(z:Sites R d φ y o X i):Era G ℝ:=
  submitted R W (s i) (cut i) (a i • c i) (φ i) (pace X i) y (o i) h z
def top (i:Fin (n+1)):Era G ℝ:=
  word ((a i/amp i) • (X i).pt) (φ i) (pace X i) y (o i) h

theorem original {L:Torch H T p v E A K}{run:XSpace.Run}{base idx f:ℕ}
    {δ η:ℝ}{fee:Fin (n+1)→ℝ}
    (file:∀i,Filed (X i) L run base idx f (amp i) δ η (fee i)
      (Shrine (plate (sectionAt R W (s i) (d i)) (cut i)) (c i))):
    MassP G ℝ n (top φ y o a X amp)=
      ∑z:((i:Fin (n+1))→Sites R d φ y o X i),MassP G ℝ n
        (fun i=>entry R W s d cut c φ y o a X i (z i)) ∧
    ∀z:((i:Fin (n+1))→Sites R d φ y o X i),
      Auth (∑i,valence (R.family.labels.level (d i)) (z i).2)
        (MassP G ℝ n (fun i=>entry R W s d cut c φ y o a X i (z i))):=by
  have paid (i)(z:Sites R d φ y o X i):Auth (valence (R.family.labels.level (d i)) z.2)
      (entry R W s d cut c φ y o a X i z):=
    WilsonIndependentMatchedOpeningPorts.paid R W _ _ _ _ _ _ _ _ _
  have cutpoints (i:Fin (n+1)):top φ y o a X amp i=∑z,entry R W s d cut c φ y o a X i z:=
    (WilsonIndependentMatchedOpeningAccrued.filed R W (s i) (cut i) (c i) (X i) (file i)
      (a i) (φ i) y (o i)).1.trans (WilsonIndependentMatchedOpeningPorts.grouped ..)
  refine ⟨?_,fun z=>manCo _ _ (fun i=>paid i (z i))⟩
  rw [funext cutpoints]
  exact WilsonIndependentMatchedOpeningMass.original (Sites R d φ y o X) d _ (fun i z=>
    (paid i z).tall (valence_cap _ _))
end YM.Integration.WilsonIndependentMatchedOpeningCensus
