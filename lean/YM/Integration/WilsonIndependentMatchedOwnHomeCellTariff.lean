import YM.Integration.WilsonIndependentMatchedOwnHomePinnedWindow
import YM.Integration.WilsonIndependentMatchedOwnHomeCellRows

/-! A common smooth optical measurement preserves the two separate thermal
bills and the signed two-cutoff saving, on this same finite vector. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeCellTariff
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

open WilsonIndependentMatchedOwnHomeCellRows (collect)
open WilsonSeparatedPrefixMovingPinCanvas (total)

theorem observed (Φ:Rarity D)(ε y:ℝ)(o:CellR)(A B δ:ℝ)(pos:0<ε)(small:ε ≤ 1)(amp:Amplitude Φ A)
    (dpos:0 ≤ δ)(L M:Cover→Lounge)(paid:∀s∈canvasM Φ ε y,∀z:CellR,twain B δ (L s z) (M s z)):
    twain ((5*radiusH Φ ε y)^4*A*B) δ
      (WilsonIndependentMatchedOwnHomeCellRows.collect Φ ε y o L)
      (WilsonIndependentMatchedOwnHomeCellRows.collect Φ ε y o M):=by
  have zero:(0:Cover)∈canvasM Φ ε y:=by
    unfold canvasM;apply Fintype.mem_piFinset.mpr;intro i
    exact Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Int.natCast_nonneg _),Int.natCast_nonneg _⟩
  have posB:0 ≤ B:=(paid 0 zero zeroC).nn
  have estimate (P:Cover→Lounge)(rate:∀s∈canvasM Φ ε y,∀z:CellR,‖P s z‖ ≤ B):
      ‖WilsonIndependentMatchedOwnHomeCellRows.collect Φ ε y o P‖ ≤ (5*radiusH Φ ε y)^4*A*B:=by
    have law:=WilsonSeparatedPrefixMovingPinCanvas.original Φ ε y o A B amp posB pos small P 0
      (fun s hs z=>by simpa only [Pi.zero_apply,ContinuousMap.zero_apply,sub_zero] using rate s hs z)
    change ‖(WilsonIndependentMatchedOwnHomeCellRows.collect Φ ε y o) P-(WilsonIndependentMatchedOwnHomeCellRows.collect Φ ε y o) 0‖ ≤ _ at law
    simpa only [map_zero,sub_zero] using law
  refine ⟨estimate L (fun s hs z=>(paid s hs z).main),estimate M (fun s hs z=>(paid s hs z).side),?_⟩
  exact (WilsonSeparatedPrefixMovingPinCanvas.original Φ ε y o A (B*δ) amp (mul_nonneg posB dpos) pos small L M
    (fun s hs z=>(paid s hs z).gap)).trans_eq (by ring)

theorem common {B δ u v:ℝ}(paid:twain B δ u v)(θ:ℝ):twain (|θ| *B) δ (θ*u) (θ*v):=by
  constructor
  · rw [norm_mul,Real.norm_eq_abs];exact mul_le_mul_of_nonneg_left paid.main (abs_nonneg _)
  · rw [norm_mul,Real.norm_eq_abs];exact mul_le_mul_of_nonneg_left paid.side (abs_nonneg _)
  · rw [←mul_sub,norm_mul,Real.norm_eq_abs,mul_assoc];exact mul_le_mul_of_nonneg_left paid.gap (abs_nonneg _)

end YM.Integration.WilsonIndependentMatchedOwnHomeCellTariff
end
