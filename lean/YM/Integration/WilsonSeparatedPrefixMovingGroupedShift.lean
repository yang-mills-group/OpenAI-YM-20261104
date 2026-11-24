import YM.Integration.WilsonSeparatedPrefixMovingGroupedOpening
import YM.Integration.WilsonSeparatedPrefixMovingPinHearing
import YM.Integration.WilsonSeparatedPrefixMovingPinProduct

/-! The source pin shifts every realized native visit together, including every rank-zero term. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingGroupedShift
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


open WilsonSeparatedPrefixMovingGroupedOpening
open WilsonSeparatedPrefixMovingPinHearing (shiftHom)
variable {G:Gauge}
private theorem slide {B U:Type}[AddGroup B](a:B)(q:Blue.Cost)(P:Pal ℝ (B×U)):
    skewV a (affix q P)=affix q (skewV a P):=by
  funext e r x
  simp only [skewV,revolve,affix,Finset.sum_apply,Pi.smul_apply]

theorem funded (q:Blue.Cost)(P:Era G ℝ)(a:Cover):
    shifted (affiled q P) a=affiled q (shifted P a):=
  Prod.ext (funext fun n=>slide (wrap n a) q (P.1 n)) (slide a q P.2)

theorem gallery {I:Type}(R:Run G)(W:Initialize G)(kind:I→Bool)(d:I→ℕ)
    (names:∀i,(R.family.labels.level (d i)).Index){D:I→ℕ}(cut:∀i,d i<D i)
    (o:I → Cover)(a:Cover)(B:Composite I):
    shifted (field R W kind d names cut o B) a=field R W kind d names cut (fun i=>a+o i) B:=by
  induction B with
  | atom i=>exact (shifted_add _ a (o i)).symm
  | pair P Q hp hq=>
    change shifted (agateV _ _) a=agateV _ _
    rw [WilsonSeparatedPrefixMovingPinProduct.grouped,hp,hq]

variable {n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (A:Levels G)(chart:ChartRatio G)(N:ℕ)(home:Fin (n+1)→ℕ)
    (v:∀i,Verse (R.family.labels.level (d i)))(φ:∀i,Rarity (D i))(y:Fin (n+1)→ℝ)(o:Fin (n+1)→CellR)
local notation "Visits" => Guests R d D A N home φ y o
local notation "offers" => fare R W kind d D cut A chart N home v φ y o
local notation "roster" => keys R d D A N home φ y o
local notation "place" => sites R d D A N home φ y o

theorem original (a:Cover):
    shiftHom a (MassP G ℝ n (posted R W kind d D cut A chart N home v φ y o))=
      ∑z:((i:Fin (n+1))→Visits i),affiled (∏i,offers i (z i))
        (field R W kind d (roster z) cut (fun i=>a+place z i) (branch n id)):=by
  rw [WilsonSeparatedPrefixMovingGroupedOpening.original,map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (funded _ _ a).trans (congrArg _ (gallery R W kind d _ cut _ a _))
end YM.Integration.WilsonSeparatedPrefixMovingGroupedShift
end
