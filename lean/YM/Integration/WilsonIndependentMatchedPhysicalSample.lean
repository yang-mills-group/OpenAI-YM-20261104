import YM.Integration.WilsonIndependentMatchedPhysicalPeerClock
import YM.Integration.WilsonIndependentMatchedRosterPlanted
/-! A measured scalar functional of the entire old and renewed ordinary return. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalSample
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentMatchedRosterPlanted (response)
variable {G:Gauge}{r:ℕ}

def value (q:ℕ)(g:ℝ)(x:Fin r→YForest G):Era G ℝ→ₗ[ℝ]ℝ where
  toFun Z:=∑j∈Finset.range (q+1),g^j*Z.2 j r x
  map_add' Z W:=by
    change (∑j∈Finset.range (q+1),g^j*(Z.2 j r x+W.2 j r x))=_
    simp only [mul_add,Finset.sum_add_distrib]
  map_smul' a Z:=by
    change (∑j∈Finset.range (q+1),g^j*(a*Z.2 j r x))=a*(∑j∈Finset.range (q+1),g^j*Z.2 j r x)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem original (q:ℕ)(g:ℝ)(x:Fin r→YForest G)(Z:Era G ℝ):
    cash q g (embed (reading Z.2 x))=(value q g x Z:ℂ):=by
  simp [WilsonPhysicalMarkedDefect.RawBank.cash,embed,WilsonOlderFreshSoftSocketKinetic.reading,value]

theorem paid (e u q:ℕ)(depth:q ≤ e)(g:ℝ)(small:|g| ≤ 1)(x:Fin 0→YForest G)
    (Z:Era G ℝ)(M:ℝ)(hearing:response e u Z M):
    ‖value q g x Z‖ ≤ ((q+1:ℕ):ℝ)*M:=by
  change ‖∑i∈Finset.range (q+1),g^i*Z.2 i 0 x‖ ≤ _
  calc
    _ ≤ ∑i∈Finset.range (q+1),‖g^i*Z.2 i 0 x‖:=norm_sum_le ..
    _ ≤ ∑_i∈Finset.range (q+1),M:=by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_pow,Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) small)).trans
        (hearing.2 i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans depth) x)
    _ = _:=by simp

end YM.Integration.WilsonIndependentMatchedPhysicalSample
