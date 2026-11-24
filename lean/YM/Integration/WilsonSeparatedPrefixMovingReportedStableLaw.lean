import YM.Integration.WilsonIndependentMatchedRosterChronology
import YM.Integration.WilsonIndependentMatchedRosterEdge

/-! The ordinary all-front product at a fine date gives its full product of
later means and one normalized first-connection term for each intervening
date. Every summand starts at its own genuine formation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingReportedStableLaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n N e:ℕ}{E:Credit}


open WilsonIndependentMatchedRosterChronology (mass)
def reading (R:Realm G (e+1) E)(m K N:ℕ)(l:Fin (n+1)→ℕ)(P:Fin (n+1)→ℕ→Era G ℝ):Era G ℝ:=
  cruises R.draws R.paid N (∑s,l s) K m (mass P (K-m))

theorem original (R:Realm G (e+1) E)(m H K N:ℕ)(cut:m ≤ H)(endAt:H ≤ K)(quiet:K ≤ N)
    (l:Fin (n+1)→ℕ)(P:Fin (n+1)→ℕ→Era G ℝ)
    (head:∀s i,i ≤ K-m → Auth (l s) (P s i))
    (pushed:∀s i,i<K-m → verseI R.draws R.paid (m+i) N (l s) (P s (i+1))=P s i):
    reading R m K N l P-reading R m H N l P=
    ∑i∈Finset.range (K-H),cruises R.draws R.paid N (∑s,l s) (H+i) m
      (DeltaGap R.draws R.paid (H+i) N (fun s=>P s (H+i+1-m)) l):=by
  have grow (u:ℕ)(hu:u ≤ K-H):reading R m (H+u) N l P=reading R m H N l P+
      ∑i∈Finset.range u,cruises R.draws R.paid N (∑s,l s) (H+i) m
        (DeltaGap R.draws R.paid (H+i) N (fun s=>P s (H+i+1-m)) l):=by
    induction u with
    | zero=>simp
    | succ u ih=>
      have j₀:m+(H+u-m)=H+u:=by omega
      have j₁:m+(H+u-m+1)=H+(u+1):=by omega
      have idx:(H+u-m)+1=H+(u+1)-m:=by omega
      have small:H+u-m<K-m:=by omega
      have edge:=WilsonIndependentMatchedRosterChronology.edge R m (H+u-m) l P (by omega:m+(H+u-m)<N)
        (fun s=>head s _ (by omega)) (fun s=>pushed s _ small)
      unfold WilsonIndependentMatchedRosterChronology.born at edge
      rw [show m+(H+u-m)+1=H+(u+1) by omega,j₀,idx] at edge
      change reading R m (H+(u+1)) N l P=reading R m (H+u) N l P+_ at edge
      rw [edge,ih (by omega),Finset.sum_range_succ]
      abel
  have paid:=grow (K-H) le_rfl
  rw [Nat.add_sub_of_le endAt] at paid
  rw [paid]
  abel
end YM.Integration.WilsonSeparatedPrefixMovingReportedStableLaw
