import YM.Integration.WilsonIndependentMatchedCoverSum

/-! The whole signed first-join field reaches the same normalized receiver,
with one uniform fee for all angular ranks and thermal orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverFlush
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoveredSeats WilsonOriginalPublicPlantedFirstJoinScale
variable {G:Gauge}{e:ℕ}{E:Credit}

theorem original (R:Realm G (e+1) E)(l r m N n u b height marks:ℕ)(endDate:m+n ≤ N)
    (P Q:ℕ → Era G ℝ)(book:Posted R l r m N n P Q)
    (hp₀:Auth l (P 0))(hp₁:Auth l (P n))(hq₀:Auth r (Q 0))(hq₁:Auth r (Q n))
    (δ A:ℝ)(hp:0<δ)(cash:0 ≤ A)(clear:1 ≤ (b:ℝ)-(height:ℝ)-(marks:ℝ)/4)
    (earn:∀i<n,let x:=paceT R.draws.S m (m+i)
      Flush e u 1 (cruises R.draws R.paid N (l+r) (m+i) m
        (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1))))
        (A*x^((b:ℝ)-(height:ℝ))*(δ/x)^((marks:ℝ)/4))):
    let total:=cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))
    let base:=agateV (P 0) (Q 0)
    Auth (l+r) (total-base) ∧ Flush e u 1 (total-base) (2*A*δ^((marks:ℝ)/4)):=by
  classical
  let join:=fun i=>cruises R.draws R.paid N (l+r) (m+i) m
    (JoinGap R.draws R.paid (m+i) N l r (P (i+1)) (Q (i+1)))
  let weight:=fun i=> let x:=radius R.draws.S m i
                      x^((b:ℝ)-(height:ℝ))*(δ/x)^((marks:ℝ)/4)
  let pay:=fun i=>A*weight i
  have ordered:(∑i∈Finset.range n,pay i) ≤ 2*A*δ^((marks:ℝ)/4):=by
    dsimp only [pay];rw [←Finset.mul_sum]
    have h:=mul_le_mul_of_nonneg_left (WilsonOriginalPublicPlantedFirstJoinScale.pay
      R.draws.S m n δ hp b height marks clear) cash
    dsimp only [weight];linarith
  have filed:cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))-
      agateV (P 0) (Q 0)=∑i∈Finset.range n,join i:=by
    rw [show cruises R.draws R.paid N (l+r) (m+n) m (agateV (P n) (Q n))=
      agateV (P 0) (Q 0)+∑i∈Finset.range n,join i from book];abel
  dsimp only
  refine ⟨(cruising R.draws R.hG R.green (Nat.le_add_right m n) endDate (hp₁.manor hq₁)).sub
    (hp₀.manor hq₀),by positivity,?_⟩
  rw [filed]
  intro j hj r hr
  simp only [Prod.snd_sum,Finset.sum_apply]
  refine (Fruit.sum (w:=pay) (fun i hi=>?_) zero_le_one).more ordered
  have h:=(earn i (Finset.mem_range.mp hi)).2 j hj r hr
  simpa only [pay,weight,WilsonIndependentMatchedCoverSum.spacing,mul_assoc] using h

end YM.Integration.WilsonIndependentMatchedCoverFlush
