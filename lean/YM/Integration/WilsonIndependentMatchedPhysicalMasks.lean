import YM.Integration.WilsonIndependentMatchedRosterSigned
/-! Exact heterogeneous mixed shelves through the very same old Wilson and nonlinear thermal chart. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalMasks
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n e:ℕ}{C:Credit}

open WilsonIndependentMatchedRosterMasks (Bits quiet choose placed)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonIndependentMatchedRosterCuts (ranks)

open private summing from YM.Integration.WilsonIndependentMatchedRosterSigned
def ranksV {n:ℕ}(f:Fin (n+1)→Bool)(k:ℕ)(h:Fin (n+1)→ℕ):ℕ:=∑j,degree (f j) k (h j)

/-- The actual complete raw-minus-fitted word, on one vacuum through every
post-capture date, consists exactly of the contributions with a signed
slot. Each summand uses its own authentic rank horizon. -/
theorem original {R:Realm G (e+1) C}{n k m s N:ℕ}(before:s ≤ m)(top:m ≤ N)(h:Fin (n+1)→ℕ)(order:∀j,h j ≤ k)
    (P Q:Fin (n+1)→Era G ℝ)(hp:∀i,Auth k (P i))(hq:∀i,Auth (h i) (Q i)):
    cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n (fun i=>P i+Q i))-
      cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q)=
    ∑j∈Finset.univ.erase (quiet n),
      cruises R.draws R.paid N (ranksV (choose n j) k h) m s (placed P Q j):=by
  classical
  have form (j:Bits n):Auth (ranksV (choose n j) k h) (placed P Q j):=by
    apply manCo _ (fun i=>degree (choose n j i) k (h i))
    intro i
    cases ok:choose n j i <;> simp only [degree,Bool.false_eq_true,if_false,if_true] <;> first | exact hp i | exact hq i
  have less (j:Bits n):ranksV (choose n j) k h ≤ (n+1)*k:=by
    have pt (i:Fin (n+1)):degree (choose n j i) k (h i) ≤ k:=by cases choose n j i <;> simp [degree,order i]
    simpa [ranksV] using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pt i)
  let L:=fun j:Bits n=>cruises R.draws R.paid N ((n+1)*k) m s (placed P Q j)
  rw [WilsonIndependentMatchedRosterMasks.deposited,summing before top _ _ (fun j _=>(form j).tall (less j))]
  change (∑ j:Bits n,L j)-cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q)=_
  have no:L (quiet n)=cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q):=by
    dsimp only [L];rw [WilsonIndependentMatchedRosterMasks.fitted]
  rw [←no,←Finset.sum_erase_add _ L (Finset.mem_univ (quiet n)),add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  exact (WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green before top _ (form j) (less j)).symm

end YM.Integration.WilsonIndependentMatchedPhysicalMasks
