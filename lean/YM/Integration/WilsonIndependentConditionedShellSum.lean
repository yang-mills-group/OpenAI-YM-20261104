import YM.Integration.WilsonIndependentConditionedShellSeries
import YM.Integration.WilsonIndependentMatchedRosterSum
/-! Sum the retained ordinary faces on the inherited normalized course at the requested stable exponent. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedShellSum
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoveredSeats WilsonOriginalPublicPlantedFirstJoinScale
open WilsonIndependentMatchedRosterChronology (mass born)
variable {G:Gauge}{e q:ℕ}{E:Credit}

theorem original (R:Realm G (e+1) E)(l:Fin (q+1)→ℕ)(m N n u b height marks:ℕ)(span:m+n≤N)
    (P:Fin (q+1)→ℕ→Era G ℝ)(head:∀s i,i≤n→Auth (l s) (P s i))
    (pushed:∀s i,i<n→verseI R.draws R.paid (m+i) N (l s) (P s (i+1))=P s i)
    (δ A H ζ:ℝ)(hp:0<δ)(finest:δ≤radius R.draws.S m n)(cash:0≤A)
    (released:ζ≤(marks:ℝ)/4)(clear:(height:ℝ)+ζ<b)
    (home:Flush e u 1 (mass P 0) H)
    (earn:∀i<n,let x:=paceT R.draws.S m (m+i)
      Flush e u 1 (cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l P i))
        (A*x^((b:ℝ)-(height:ℝ))*(δ/x)^((marks:ℝ)/4))):
    let total:=cruises R.draws R.paid N (∑s,l s) (m+n) m (mass P n)
    Auth (∑s,l s) total ∧ Flush e u 1 total (H+A*WilsonIndependentConditionedShellSeries.wage b height ζ*δ^ζ):=by
  classical
  let join:=fun i=>cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l P i)
  let weight:=fun i=> let x:=radius R.draws.S m i
                      x^((b:ℝ)-(height:ℝ))*(δ/x)^((marks:ℝ)/4)
  let pay:=fun i=>A*weight i
  have ordered:(∑i∈Finset.range n,pay i) ≤ A*WilsonIndependentConditionedShellSeries.wage b height ζ*δ^ζ:=by
    dsimp only [pay];rw [←Finset.mul_sum]
    have h:=mul_le_mul_of_nonneg_left (WilsonIndependentConditionedShellSeries.pay
      R.draws.S m n δ b height ((marks:ℝ)/4) ζ hp finest released clear) cash
    dsimp only [weight];simpa only [mul_assoc] using h
  dsimp only
  have nn:=home.1
  have wage:= (WilsonIndependentConditionedShellSeries.positive clear).le
  refine ⟨cruising R.draws R.hG R.green (Nat.le_add_right m n) span (manCo _ _ (fun s=>head s _ le_rfl)),
    by positivity,?_⟩
  rw [WilsonIndependentMatchedRosterChronology.original R m N n span l P head pushed]
  intro j hj r hr
  simp only [Prod.snd_add,Pi.add_apply,Prod.snd_sum,Finset.sum_apply]
  refine Award.plus (home.2 j hj r hr) ((Fruit.sum (w:=pay) (fun i hi=>?_) zero_le_one).more ordered)
    (hedge_nn zero_le_one)
  have h:=(earn i (Finset.mem_range.mp hi)).2 j hj r hr
  simpa only [pay,weight,WilsonIndependentMatchedCoverSum.spacing,mul_assoc] using h

end YM.Integration.WilsonIndependentConditionedShellSum
