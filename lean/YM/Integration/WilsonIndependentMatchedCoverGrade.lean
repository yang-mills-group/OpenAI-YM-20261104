import YM.Integration.WilsonIndependentMatchedCoverCarried

/-! A higher truncation of the angular rank counts exactly the same
normalized Wilson transfer on an admitted lower-rank source. Each finite
torus has zero omitted Wick coefficients. Its actual cover limit is unique. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverGrade
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{k l m N b:ℕ}

private lemma determined (P Q:Era G ℝ)(hp:Auth k P)(hq:Auth l Q)(finite:P.1=Q.1):P=Q:=by
  refine Prod.ext finite (funext fun i=>funext fun r=>?_ )
  apply (hp.wing i r).exten
  rw [finite]
  exact hq.wing i r

theorem verse (A:Levels G)(Ñ:ChartRatio G)(g:G.Simple)(fund:LocalRatio Ñ)
    (live:m<N)(P:Era G ℝ)(auth:Auth k P)(more:k ≤ l):
    verseI A Ñ m N k P=verseI A Ñ m N l P:=by
  have thick:=auth.tall more
  apply determined _ _ (auth.verse A live g fund) (thick.verse A live g fund)
  funext n
  let p:=ll A m
  let K:=A.clock.kernel
  let S:=stepAt p K n
  let F:=xree p K n
  let H:=freeForms A N (m+1)
  let M:=roam A N m n
  let vac:=(story A Ñ N (m+1)).1 (n*p.L)
  let word:=P.1 (n*p.L)
  change Blue.mix (ratioHigh A Ñ N m) (reed S F H M Ñ vac k word)=Blue.mix _ (reed S F H M Ñ vac l word)
  apply congrArg (Blue.mix (ratioHigh A Ñ N m))
  funext i
  unfold WilsonCoeffUV.reed
  apply congrArg (fade plug)
  have stopped:=srStops S F H M k ((old A Ñ g fund N (m+1) live).basis _).lamp fund (auth.span (n*p.L))
  refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
  intro j _ hj
  have later:1+k+3*i ≤ j:=by simpa using hj
  exact funext fun r=> stopped j i r (Or.inr (by omega))

theorem carried (A:Levels G)(Ñ:ChartRatio G)(g:G.Simple)(fund:LocalRatio Ñ)
    (before:b ≤ m)(top:m ≤ N)(P:Era G ℝ)(auth:Auth k P)(more:k ≤ l):
    cruises A Ñ N k m b P=cruises A Ñ N l m b P:=by
  induction before using Nat.decreasingInduction with
  | self=>rw [cruises_top,cruises_top]
  | of_succ i hi ih=>
    rw [cruises_sub _ _ _ _ _ hi,cruises_sub _ _ _ _ _ hi,←ih]
    exact verse A Ñ g fund (hi.trans_le top) _ (cruising A g fund hi top auth) more

end YM.Integration.WilsonIndependentMatchedCoverGrade
