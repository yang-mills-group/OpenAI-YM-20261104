import YM.Integration.WilsonIndependentFittedProductCensus

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedClocks
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedReportedFilm (funded)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}

theorem returned (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N K s m i:ℕ)(common:m+i=K)(before:s ≤ m)(cap:K ≤ N)(c:Cost):
    clock A O N K s (reel (relativeC A O N m i) c)=clock A O N m s c:=by
  calc
    _=clock A O N (m+i) s (reel (relativeC A O N m i) c):=by rw [common]
    _=clock A O N m s (clock A O N (m+i) m (reel (relativeC A O N m i) c)):=
      (WilsonOlderFreshSoftSocketKinetic.combine A O N (m+i) m s before (Nat.le_add_right ..) _).symm
    _=_:=by rw [WilsonIndependentFittedRelativeClock.restored A O simple localO N m i (common.le.trans cap)]

theorem original (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N K s:ℕ)(cap:K ≤ N)(n:ℕ)(l m i:Fin (n+1) → ℕ)
    (I:Fin (n+1) → Type)[∀j,Fintype (I j)]
    (c:(j:Fin (n+1)) → I j → Cost)(P Q:(j:Fin (n+1)) → I j → Era G ℝ)
    (dates:∀j,m j+i j=K)(before:∀j,s ≤ m j)
    (high:∀j t,Auth (l j) (P j t))(low:∀j t,Auth (l j) (Q j t))
    (filed:∀j t,P j t=funded (reel (relativeC A O N (m j) (i j)) (c j t)) (Q j t))
    (r:ℕ)(x:Fin r → YForest G):
    reading (cruises A O N (∑j,l j) K s (MassP G ℝ n (fun j=>∑t,P j t))).2 x=
      ∑w:(j:Fin (n+1)) → I j,(∏j,clock A O N (m j) s (c j (w j)))*
        reading (cruises A O N (∑j,l j) K s (MassP G ℝ n (fun j=>Q j (w j)))).2 x:=by
  let upper:=fun j t=>reel (relativeC A O N (m j) (i j)) (c j t)
  have paid (j:Fin (n+1))(t:I j):P j t=funded (reel (relativeC A O N K 0) (upper j t)) (Q j t):=by
    have same (a:Cost):reel (relativeC A O N K 0) a=a:=by simp [relativeC,leeB]
    rw [same]; exact filed j t
  have endK:s ≤ K:=by rw [←dates 0];exact (before 0).trans (Nat.le_add_right ..)
  have sold:=WilsonIndependentFittedProductCensus.stopped A O simple localO N K 0 s endK
    (by simpa only [Nat.add_zero] using cap) n l I upper P Q high low paid r x
  simp only [Nat.add_zero] at sold
  refine sold.trans (sum_congr rfl ?_)
  intro w _
  congr 1
  exact prod_congr rfl (fun j _=>returned A O simple localO N K s (m j) (i j) (dates j) (before j) cap (c j (w j)))

end YM.Integration.WilsonIndependentMovingFittedClocks
