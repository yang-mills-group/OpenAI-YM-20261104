import YM.Integration.WilsonIndependentMatchedOwnHomeForestTariff
import YM.Integration.WilsonIndependentMatchedOwnHomeLowThermal

/-! The public aperture and both spatial rulers are attached to the same
three filtered columns in the low- and high-order returns. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeForkWindow
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedCoverProfile (word)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedOwnHomePinnedPlacement (moved)
open WilsonIndependentMatchedOwnHomePinnedMaster (point)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonSeparatedPrefixMovingPinHearing (hear shiftHom)
open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{n e:ℕ}{E:Credit}

open WilsonIndependentMatchedOwnHomePinnedRoster (translated)
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Power WilsonCoeffUV.Mer.Patrol
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReportedBasis (price)
open WilsonIndependentSpoutMasterCutoff (Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentSpoutMasterBasisCutoff (bank)
open WilsonIndependentSpoutMasterReport (report)
variable {D h l:ℕ}

open WilsonIndependentMatchedOwnHomePinnedWindow (size)
open WilsonIndependentMatchedOwnHomeIntegratedClock (chart)
open WilsonIndependentMatchedOwnHomeIntegratedMaster (entry)

open WilsonMovingForkSharpSections (publicFrame)
open WilsonIndependentMatchedOwnHomeForestTariff
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
variable {D':ℕ}
def ranks (D D':ℕ):Fin 3→ℕ:=Fin.cons D' (fun _=>D)
theorem fits (p:4<D)(pF:4<D'):(i:Fin 3)→4<ranks D D' i:=Fin.cases pF (fun _=>p)
theorem same (P:Run G)(p:4<D)(pF:4<D'):
    WilsonIndependentMatchedOwnHomeForestTariff.all (publicFrame P) p pF=deck (G:=G) (fun _:Fin 3=>4) (ranks D D') (fits p pF):=by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> rfl

theorem original (P:Run G)(p:4<D)(pF:4<D'){H:Hol G}{anchor low mem:ℕ}{main hold clock pay teach:Credit}
    (sale:Earned P (fun _:Fin 3=>4) (ranks D D') (fits p pF) anchor low mem main hold)(fees:Paid P anchor low clock)
    (R:Realm G (e+1) E)(levels:R.draws=P.family.path.levels)(vac:R.paid=P.metals.O)
    (m t old K N:ℕ)(openAt:anchor ≤ old)(awake:R.anchor ≤ K)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N)(onset:t ≤ m):
    let Q:=WilsonIndependentMatchedOwnHomeForestTariff.all (publicFrame P) p pF
    ∀(_fund:HorizonP H R pay teach Q)(a:∀i,Alma (Q i).F)(φ:Wilt Q)(Φ:Rarity D)(y:ℝ)(o:CellR)(ρ:ℝ)
      (room amp:ℝ)(B:Fin 3→ℝ),Amplitude Φ amp → Compar R.draws.S (zz R.draws) old m ≤ room →
      Bough Q φ (paceT R.draws.S m m) room B → ∀(J:ℕ)(_order:J ≤ low)(g:ℝ)(_small:|g| ≤ 1),
      let ε:=paceT R.draws.S t m
      let Z:=room+size R.draws.S Φ m t m y
      let wage:=fun j=>|ρ^4| *((5*radiusH Φ ε y)^4*amp*price P main hold clock old m j Z B)
      let F:=fun N₀=>WilsonIndependentMatchedOwnHomeIntegratedMaster.entry R Q φ (bank Q a) Φ y o t m m old K N₀ ρ
      let A:=embed (F N-F K)
      ‖PowerSeries.coeff 0 A‖ ≤ wage 0*trailC R.draws.S m K ∧
      ‖cash J g A‖ ≤ (∑i∈Finset.range (J+1),wage i)*trailC R.draws.S m K:=by
  rw [same P p pF]
  intro Q fund a φ Φ y o ρ room amp B amplitude optic bough J order g small
  have quote:=WilsonIndependentMatchedOwnHomeLowThermal.original P (fun _:Fin 3=>4) (ranks D D') (fits p pF) sale fees R levels vac fund
    m t m old K N openAt awake ear cut top onset cut a φ Φ y o ρ room amp B amplitude
    (levels ▸ optic) (levels ▸ bough) J order g small
  simpa only [levels] using quote

end YM.Integration.WilsonIndependentMatchedOwnHomeForkWindow
end
