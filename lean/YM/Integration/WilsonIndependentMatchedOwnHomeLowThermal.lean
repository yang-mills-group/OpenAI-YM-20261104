import YM.Integration.WilsonIndependentMatchedOwnHomeLowCells
import YM.Integration.WilsonIndependentFittedRosterCash

/-! The truly ordered lower part of the finite thermal position measurement,
at its own elected order and before the planting depth. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeLowThermal
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
variable (P:Run G)(L d:Fin (n+1)→ℕ)(admit:∀i,L i<d i)
local notation "Q₀" => deck (G:=G) L d admit
local notation "A₀" => P.family.path.levels
local notation "O₀" => P.metals.O


open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
theorem original {H:Hol G}{anchor low mem:ℕ}{main basis clock pay teach:Credit}
    (sale:Earned P L d admit anchor low mem main basis)(fees:Paid P anchor low clock)
    (R:Realm G (e+1) E)(levels:R.draws=A₀)(vac:R.paid=O₀)(granted:HorizonP H R pay teach Q₀)
    (m t c old K N:ℕ)(openAt:anchor ≤ old)(awake:R.anchor ≤ K)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N)
    (onset:t ≤ c)(enrolled:c ≤ K)(a:∀i,Alma (Q₀ i).F)(φ:Wilt Q₀)(Φ:Rarity D)(y:ℝ)(o:CellR)(ρ:ℝ)
    (room amp:ℝ)(B:Fin (n+1)→ℝ)(amplitude:Amplitude Φ amp)(optic:Compar (A₀).S (zz A₀) old m ≤ room)
    (bough:Bough Q₀ φ (paceT (A₀).S m c) room B)(J:ℕ)(order:J ≤ low)(g:ℝ)(small:|g| ≤ 1):
    let ε:=paceT (A₀).S t c
    let Z:=room+size (A₀).S Φ m t c y
    let wage:=fun i=> |ρ^4| *((5*radiusH Φ ε y)^4*amp*price P main basis clock old m i Z B)
    let F:=fun N₀=>WilsonIndependentMatchedOwnHomeIntegratedMaster.entry R Q₀ φ (bank Q₀ a) Φ y o t m c old K N₀ ρ
    let A:=embed (F N-F K)
    ‖PowerSeries.coeff 0 A‖ ≤ wage 0*trailC (A₀).S m K ∧
    ‖cash J g A‖ ≤ (∑i∈Finset.range (J+1),wage i)*trailC (A₀).S m K:=by
  intro ε Z wage F A
  have tested (i:ℕ)(hi:i ≤ J):‖PowerSeries.coeff i A‖ ≤ wage i*trailC (A₀).S m K:=by
    have coef:=WilsonIndependentMatchedOwnHomeLowCells.original P L d admit sale fees R levels vac granted m t c old K N openAt awake ear cut top onset enrolled a φ Φ y o ρ room amp B amplitude optic bough i (hi.trans order)
    dsimp only [A,embed]
    rw [PowerSeries.coeff_map,map_sub]
    exact (Complex.norm_real _).le.trans coef.gap
  refine ⟨tested 0 (Nat.zero_le _),?_⟩
  unfold WilsonPhysicalMarkedDefect.RawBank.cash
  rw [Finset.sum_mul]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro i hi
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg g) small)).trans (tested _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

end YM.Integration.WilsonIndependentMatchedOwnHomeLowThermal
end
