import YM.Integration.WilsonIndependentMatchedReportedCensusWage
import YM.Integration.WilsonIndependentMatchedPhysicalReportedCash
/-! The restored mixed principal income on the true finite radiation
shoulder only demands the measured direction; its formal gross is used in
the discarded numerical orders. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedMarket
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Next.Foundations PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open WilsonIndependentMatchedPhysicalSector (Courts)
open WilsonIndependentMatchedPhysicalReportedFilm (sponsors)
open WilsonIndependentMatchedRosterMasks (Bits quiet choose)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonIndependentMatchedPhysicalReportedClock (bill)
open WilsonIndependentMatchedPhysicalReportedPeer (measured)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n a k u₀ e:ℕ}
local notation "CC" => Credit.leanC
local notation "I" => Fin (n+1)

def price {H:Hol G}{Q:Fin (a+1) → SealR G}{v:∀i,Rails (Q i).h k u₀ e}
    (V:Realm G (e+1) CC)(X:Courts (H:=H) (v:=v))(u b out host m K q:ℕ)(B J:Fin (a+1) → Credit)
    (primary:Fin (a+1) → Credit)(mid last:(Fin (a+1) → Bool)→Credit)(Z g cost:ℝ)(sizes:Fin (a+1)→ℝ):ℝ:=
  ∑j∈Finset.univ.erase (quiet a),let f:=choose a j
  ((∏i,measured (Q i) (X i) q g (B i) m V.draws (f i))+
   (((a+1:ℕ):ℝ)+1)*|g|^(q+1)*∏i,WilsonIndependentMatchedPhysicalReportedPeer.reserve (X i) q (J i) (f i))*
   |bill q cost (WilsonIndependentMatchedPhysicalAxes.charge V X f u b out host m K
       primary (mid f) (last f) Z⁻¹ (2*Z+1) sizes)|

theorem issued (R:Run G)(l d:I→ℕ)(admit:∀i,l i<d i)(own:∀i,Rails (l i) k u₀ e)
    (floor:ℕ)(B J:I→Credit)(earned:WilsonIndependentMatchedReportedCensusWage.Enrolled R l d admit own floor B J)
    (V:Realm G (e+1) CC)(m K N:ℕ)(wake:floor ≤ m)(start:m ≤ K)(live:K ≤ N)
    (X:∀i,CutsP (hol G) ((deck (G:=G) l d admit) i).ans ((deck (G:=G) l d admit) i).path (own i) CC CC CC CC)
    (file:∀i,(X i).ax=R.family.path.levels ∧ (X i).tx=R.metals.O ∧ (X i).N=N ∧ (X i).m=m)
    (lev:V.draws=R.family.path.levels)(leg:Fin (a+1)→I)(u b out host q:ℕ)(depth:q ≤ e)(Z g cost:ℝ)
    (primary:Fin (a+1)→Credit)(mid last:(Fin (a+1)→Bool)→Credit)(sizes:Fin (a+1)→ℝ):
    let Q:=deck (G:=G) l d admit
    WilsonIndependentMatchedPhysicalReportedCash.price (Q:=Q ∘ leg) (v:=fun i=>own (leg i))
      V (fun i=>X (leg i)) u b out host m K q primary mid last Z g cost sizes ≤
    price (Q:=Q ∘ leg) (v:=fun i=>own (leg i)) V (fun i=>X (leg i)) u b out host m K q (B ∘ leg)
      (J ∘ leg) primary mid last Z g cost sizes:=by
  intro Q
  apply Finset.sum_le_sum
  intro j _
  let f:=choose a j
  let data:=sponsors (Q:=Q ∘ leg) (v:=fun i=>own (leg i)) (fun i=>X (leg i)) f
  have paid:=earned m K N wake start live X file leg f q g depth
  let c:=(((a+1:ℕ):ℝ)+1)*|g|^(q+1)
  have positive:0 ≤ c:=by dsimp [c]; positivity
  let M:=bill q cost (WilsonIndependentMatchedPhysicalAxes.charge (Q:=Q ∘ leg) (v:=fun i=>own (leg i))
    V (fun i=>X (leg i)) f u b out host m K primary (mid f) (last f) Z⁻¹ (2*Z+1) sizes)
  have nn:0 ≤ numerical q g data+c*reserve q data:=add_nonneg
    (prod_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _)
    (mul_nonneg positive (prod_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _))
  apply (mul_le_mul_of_nonneg_left (le_abs_self M) nn).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg M)
  dsimp only [Function.comp_apply]
  rw [lev]
  exact add_le_add paid.1 (mul_le_mul_of_nonneg_left paid.2 positive)
end YM.Integration.WilsonIndependentMatchedReportedMarket
