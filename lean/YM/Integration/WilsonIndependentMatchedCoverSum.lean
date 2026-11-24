import YM.Integration.WilsonIndependentMatchedCoveredSeats
import YM.Integration.WilsonIndependentMatchedCoverJoined
import YM.Integration.WilsonOriginalPublicPlantedFirstJoinScale

/-! Sum the genuine signed first joins on the original covered two-source
itinerary while retaining its independent arrived no-join field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverSum
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoveredSeats WilsonOriginalPublicPlantedFirstJoinScale
variable {G:Gauge}{e:ℕ}{E:Credit}

lemma spacing (S:Schedule)(m i:ℕ):radius S m i=paceT S m (m+i):=by
  simp only [radius,Schedule.scale,Real.log_inv]
  rw [show -(-Real.log (S.a (m+i)) - -Real.log (S.a m)) =
      Real.log (S.a (m+i)) - Real.log (S.a m) by ring,
    Real.exp_sub,Real.exp_log (S.a_pos _),Real.exp_log (S.a_pos _)]
  rfl

def scalar (j:ℕ)(q:Fin 0 → YForest G):Era G ℝ  →+ ℝ where
  toFun := fun X=>X.2 j 0 q
  map_zero' := rfl
  map_add' := fun _ _=>rfl

/-- In particular no prior occupied unit is deducted from the summands of
this older, normalized hearing. The base includes both held scalar feeds. -/
theorem signed (R:Realm G (e+1) E)(l r m N n u b height marks:ℕ)
    (P Q:ℕ → Era G ℝ)(book:Posted R l r m N n P Q)(δ A:ℝ)(hp:0<δ)(cash:0 ≤ A)
    (clear:1 ≤ (b:ℝ)-(height:ℝ)-(marks:ℝ)/4)
    (earn:∀i<n,let x:=paceT R.draws.S m (m+i)
      Flush e u 1 (cruises R.draws R.paid N (l+r) (m+i) m
        (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))))
        (A*x^((b:ℝ)-(height:ℝ))*(δ/x)^((marks:ℝ)/4))):
    ∀j ≤ e,∀q:Fin 0 → YForest G,
    ‖(cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))).2 j 0 q-
        (agateV (P 0) (Q 0)).2 j 0 q‖ ≤ 2*A*δ^((marks:ℝ)/4):=by
  intro j hj q
  let f:=scalar j q
  let join:=fun i=>cruises R.draws R.paid N (l+r) (m+i) m
        (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1)))
  have file:=congrArg f book
  rw [map_add,map_sum] at file
  refine WilsonOriginalPublicPlantedFirstJoinScale.signed R.draws.S m n δ hp b height marks clear
    A cash _ _ (fun i=>f (join i)) file ?_
  intro i hi
  rw [spacing]
  exact WilsonIndependentMatchedCoverJoined.unit (earn i hi) j hj q

end YM.Integration.WilsonIndependentMatchedCoverSum
