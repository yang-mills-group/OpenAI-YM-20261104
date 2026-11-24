import YM.Integration.WilsonIndependentMatchedOpeningHomes
import YM.Integration.WilsonMovingForkSharpNativeSeal

/-! Exact group-word enrollment of the entire independent Mer input on each arm's true ruler and actual marked upper. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingGroupedOpening
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
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open RegulatorIR.Cluster
open WilsonIndependentMatchedOpeningCensus (entry pace Sites)
open WilsonIndependentRawRosterWord (degree)
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.StableStrip WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket
open PhysicalNext PhysicalNext.Repeat Next.Foundations
open WilsonIndependentMatchedOpeningComposite (money branch canonical)
open WilsonIndependentMatchedOpeningFee (risk)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedNamedPair (sectionAt)

variable {G:Gauge}{n:ℕ}
variable (R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (A:Levels G)(chart:ChartRatio G)(N:ℕ)(home:Fin (n+1)→ℕ)
    (v:∀i,Verse (R.family.labels.level (d i)))(φ:∀i,Rarity (D i))(y:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)
def pitch (i:Fin (n+1)):=paceT A.S (home i) N
def bill (i:Fin (n+1)):=steep A chart (sectionAt R W (kind i) (d i)) (cut i) N (home i) (N-home i) (v i)
abbrev Guests (i:Fin (n+1)):=Port (R.family.labels.level (d i)) (φ i) (pitch A N home i) (y i) (o i)
def posted (i:Fin (n+1)):Era G ℝ:=locale (o i) (FirstCharge A chart (sectionAt R W (kind i) (d i)) (cut i)
  (φ i) (home i) N N (y i) (v i))
def recorded (i:Fin (n+1))(z:Guests R d D A N home φ y o i):Era G ℝ:=
  submitted R W (kind i) (cut i) (bill R W kind d D cut A chart N home v i)
    (φ i) (pitch A N home i) (y i) (o i) (d i) z
def fare (i:Fin (n+1))(z:Guests R d D A N home φ y o i):Blue.Cost:=
  PowerSeries.C (drumB (d i) (pitch A N home i))*
    realDose R (w:=cut i) (wheelC (pitch A N home i) (y i) z.1.val (φ i).ψ (o i))
      (bill R W kind d D cut A chart N home v i) z.2
def keys (z:∀i,Guests R d D A N home φ y o i)(i:Fin (n+1)):=sheet (R.family.labels.level (d i)) (z i).2
def sites (z:∀i,Guests R d D A N home φ y o i)(i:Fin (n+1)):Cover:=(z i).1.val

theorem file (i:Fin (n+1)):posted R W kind d D cut A chart N home v φ y o i=
    ∑z:Guests R d D A N home φ y o i,recorded R W kind d D cut A chart N home v φ y o i z:=by
  let M:=sectionAt R W (kind i) (d i)
  let u:=bill R W kind d D cut A chart N home v i
  change word (Shrine (Peaks A chart M (cut i) N N) u) (φ i) (pitch A N home i) (y i) (o i) (d i)=_
  rw [Peak_initial]
  exact (WilsonIndependentMatchedOpeningProfile.original R W (kind i) (cut i) u (φ i) _ (y i) (o i) (d i) (pace_pos ..)).trans
    (WilsonIndependentMatchedOpeningPorts.grouped R W (kind i) (cut i) u (φ i) _ (y i) (o i) (d i))

theorem original:
    MassP G ℝ n (posted R W kind d D cut A chart N home v φ y o)=
      ∑z:((i:Fin (n+1))→Guests R d D A N home φ y o i),
        affiled (∏i,fare R W kind d D cut A chart N home v φ y o i (z i))
          (field R W kind d (keys R d D A N home φ y o z) cut (sites R d D A N home φ y o z) (branch n id)):=by
  let rows:=recorded R W kind d D cut A chart N home v φ y o
  have paid (i)(z:Guests R d D A N home φ y o i):Auth (d i) (rows i z):=
    (WilsonIndependentMatchedOpeningPorts.paid R W _ _ _ _ _ _ _ _ z).tall (valence_cap _ _)
  rw [funext (file R W kind d D cut A chart N home v φ y o),
    WilsonIndependentMatchedOpeningMass.original (Guests R d D A N home φ y o) d rows paid]
  apply Finset.sum_congr rfl
  intro z _
  let names:=keys R d D A N home φ y o z
  let loc:=sites R d D A N home φ y o z
  let cost (i:Fin (n+1)):=fare R W kind d D cut A chart N home v φ y o i (z i)
  let source (i:Fin (n+1)):=column R W (kind i) (cut i) (seat (R.family.labels.level (d i)) (names i)) (loc i)
  have entries (i:Fin (n+1)):rows i (z i)=affiled (cost i) (source i):=by
    exact WilsonIndependentMatchedOpeningComposite.money .. 
  have authentic (i:Fin (n+1)):Auth (degree R d names i) (source i):=
    WilsonIndependentMatchedOpeningRoster.enrolled R W kind d _ cut _ (.atom i)
  rw [funext entries,risk source _ authentic cost]
  exact congrArg _ (canonical R W kind d _ cut _ (id:(Fin (n+1))→(Fin (n+1))))
end YM.Integration.WilsonSeparatedPrefixMovingGroupedOpening
end
