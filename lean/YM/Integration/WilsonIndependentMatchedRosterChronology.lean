import YM.Integration.WilsonIndependentMatchedRosterEdge

/-! The ordinary all-front product at a fine date gives its full product of
later means and one normalized first-connection term for each intervening
date. Every summand starts at its own genuine formation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterChronology
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n N e:ℕ}{E:Credit}

def mass (P:Fin (n+1)→ℕ→Era G ℝ)(j:ℕ):Era G ℝ:=MassP G ℝ n (fun s=>P s j)
def born (R:Realm G (e+1) E)(m N:ℕ)(l:Fin (n+1)→ℕ)(P:Fin (n+1)→ℕ→Era G ℝ)(i:ℕ):Era G ℝ:=
  DeltaGap R.draws R.paid (m+i) N (fun a=>P a (i+1)) l

theorem edge (R:Realm G (e+1) E)(m i:ℕ)(l:Fin (n+1)→ℕ)(P:Fin (n+1)→ℕ→Era G ℝ)
    (date:m+i<N)(head:∀s,Auth (l s) (P s (i+1)))
    (step:∀s,verseI R.draws R.paid (m+i) N (l s) (P s (i+1))=P s i):
    cruises R.draws R.paid N (∑s,l s) (m+i+1) m (mass P (i+1)) =
      cruises R.draws R.paid N (∑s,l s) (m+i) m (mass P i)+
      cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l P i):=by
  have fine:=Auth.verse R.draws date R.hG R.green (manCo (fun s=>P s (i+1)) l head)
  have coarse:=manCo (fun s=>P s i) l (fun s=>step s ▸ Auth.verse R.draws date R.hG R.green (head s))
  change Auth (∑s,l s) (verseI R.draws R.paid (m+i) N (∑s,l s) (mass P (i+1))) at fine
  change Auth (∑s,l s) (mass P i) at coarse
  have cash:born R m N l P i=verseI R.draws R.paid (m+i) N (∑s,l s) (mass P (i+1))-mass P i:=by
    unfold born DeltaGap startK mass
    simp only [step]
  rw [cash,cruisePlus R.draws (Nat.le_add_right _ _) R.hG R.green date.le fine coarse,
    cruiseStep R.draws R.paid _ (Nat.le_add_right _ _)]
  abel

theorem original (R:Realm G (e+1) E)(m N h:ℕ)(top:m+h≤N)(l:Fin (n+1)→ℕ)(P:Fin (n+1)→ℕ→Era G ℝ)
    (head:∀s i,i≤h→Auth (l s) (P s i))(step:∀s i,i<h→verseI R.draws R.paid (m+i) N (l s) (P s (i+1))=P s i):
    cruises R.draws R.paid N (∑s,l s) (m+h) m (mass P h)=mass P 0+
      ∑i∈Finset.range h,cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l P i):=by
  induction h with
  | zero=>simp [cruises_top]
  | succ h ih=>
    have prior:=ih (by omega) (fun s i hi=>head s i (by omega)) (fun s i hi=>step s i (by omega))
    rw [Finset.sum_range_succ,←add_assoc (mass P 0) _ _,←prior]
    exact edge R m h l P (by omega) (fun s=>head s _ le_rfl) (fun s=>step s h (Nat.lt_succ_self _))

end YM.Integration.WilsonIndependentMatchedRosterChronology
