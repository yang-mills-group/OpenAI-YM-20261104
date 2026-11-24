import YM.Integration.WilsonIndependentMatchedPhysicalReportedClock

/-! Real numerical hearing, with the old-N nonlinear reporting reset applied
to the complete signed scalar on the original older retained field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalReportedSample
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentMatchedPhysicalReportedClock (bill)
open scoped BigOperators Topology Classical
variable {G:Gauge}{r:ℕ}

def heard (x:Fin r→YForest G):Era G ℝ →+ Cost where
  toFun Z:=reading Z.2 x
  map_zero':=by
    ext1 i
    rw [map_zero]
    rfl
  map_add' Z W:=by
    ext1 i
    rw [map_add]
    rfl

def value (L:Levels G)(O:ChartRatio G)(N m host q:ℕ)(g:ℝ)(x:Fin r→YForest G):Era G ℝ →+ ℝ:=
  (WilsonIndependentMatchedPhysicalPeer.reading q g).toAddMonoidHom.comp
    ((reel (relativeC L O N host (m-host))).toAddMonoidHom.comp (heard x))

theorem original (L:Levels G)(O:ChartRatio G)(N m host q:ℕ)(g:ℝ)(x:Fin r→YForest G)(Z:Era G ℝ):
    cash q g (embed (report L O N m host (reading Z.2 x)))=(value L O N m host q g x Z:ℂ):=by
  change WilsonPhysicalMarkedDefect.RawBank.cash q g (embed (report L O N m host (reading Z.2 x)))=
    (WilsonIndependentMatchedPhysicalPeer.reading q g (report L O N m host (reading Z.2 x)):ℂ)
  simp [WilsonPhysicalMarkedDefect.RawBank.cash,embed,WilsonIndependentMatchedPhysicalPeer.reading,Finset.sum_apply]

theorem paid (R:Run G){j e:ℕ}{D:Credit}(fees:Paid R j e D)(host m N:ℕ)
    (early:j ≤ host)(older:host ≤ m)(live:m ≤ N)(q u:ℕ)(depth:q ≤ e)(g:ℝ)(small:|g| ≤ 1)
    (x:Fin 0→YForest G)(Z:Era G ℝ)(M:ℝ)(fee:response e u Z M):
    ‖value R.family.path.levels R.metals.O N m host q g x Z‖ ≤
      bill q (D.buy (Compar R.family.S (zz R.family.path.levels) host m)) M:=by
  let A:=reading Z.2 x
  let Y:=report R.family.path.levels R.metals.O N m host A
  change ‖WilsonIndependentMatchedPhysicalPeer.reading q g Y‖ ≤ _
  simp only [WilsonIndependentMatchedPhysicalPeer.reading,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply (norm_sum_le ..).trans
  unfold bill
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_pow,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) small)).trans
  apply WilsonIndependentMatchedPhysicalReportedClock.coefficient R fees host m N early older live A M fee.1.1
  · intro t ht
    simpa only [A,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk] using fee.2 t ht x
  · exact (Nat.le_of_lt_succ (mem_range.mp hi)).trans depth

end YM.Integration.WilsonIndependentMatchedPhysicalReportedSample
