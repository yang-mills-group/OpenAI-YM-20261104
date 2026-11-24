import YM.Integration.WilsonIndependentFittedPivotRoster
import YM.Integration.WilsonIndependentMatchedRosterMasks

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedProductClock
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedReportedFilm (funded)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}

theorem ordinary (n:ℕ)(c:Fin (n+1)→ Cost)(P:Fin (n+1)→Era G ℝ):
    MassP G ℝ n (fun j=>funded (c j) (P j))=funded (∏j,c j) (MassP G ℝ n P):=by
  induction n with
  | zero=>rw [Fin.prod_univ_succ,Fintype.prod_empty,mul_one];rfl
  | succ n ih=>
    change agateV (funded (c 0) (P 0)) (MassP G ℝ n (fun i=>funded (c i.succ) (P i.succ)))=_
    conv_rhs => rw [Fin.prod_univ_succ]
    rw [ih (fun j=>c j.succ) (fun j=>P j.succ)]
    exact Prod.ext (funext fun j=>by
      change woad (affix _ _) (affix _ _)=affix _ (woad _ _)
      rw [WilsonIndependentFittedThermalProduct.left,WilsonIndependentFittedThermalProduct.right,affix_mul]
      rfl)
      (by change woad (affix _ _) (affix _ _)=affix _ (woad _ _)
          rw [WilsonIndependentFittedThermalProduct.left,WilsonIndependentFittedThermalProduct.right,affix_mul]
          rfl)

theorem applied (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N m i s:ℕ)(before:s≤ m)(endN:m+i≤N)(n:ℕ)(l:Fin (n+1)→ℕ)
    (c:Fin (n+1)→ Cost)(P Q:Fin (n+1)→Era G ℝ)(high:∀j,Auth (l j) (P j))
    (low:∀j,Auth (l j) (Q j))
    (filed:∀j,P j=funded (reel (relativeC A O N m i) (c j)) (Q j))
    (r:ℕ)(x:Fin r→YForest G):
    reading (cruises A O N (∑j,l j) (m+i) s (MassP G ℝ n P)).2 x=
      (∏j,clock A O N m s (c j))*reading (cruises A O N (∑j,l j) (m+i) s (MassP G ℝ n Q)).2 x:=by
  have eqn:MassP G ℝ n P=funded (reel (relativeC A O N m i) (∏j,c j)) (MassP G ℝ n Q):=by
    rw [show P=fun j=>funded (reel (relativeC A O N m i) (c j)) (Q j) from funext filed,ordinary,map_prod]
  have upper:=manCo P l high
  have lower:=manCo Q l low
  have stop:=before.trans (Nat.le_add_right m i)
  have paid:=WilsonOlderFreshSoftSocketHistory.original A O simple localO N (∑j,l j) (m+i) s stop endN
    (MassP G ℝ n P) (MassP G ℝ n Q) _ upper lower
    (fun j=>congrArg (fun f:Era G ℝ=>f.1 j) eqn)
  rw [paid,WilsonOlderFreshSoftSocketKinetic.valued,←WilsonOlderFreshSoftSocketKinetic.combine A O N (m+i) m s
    before (Nat.le_add_right ..),WilsonIndependentFittedRelativeClock.restored A O simple localO N m i endN]
  have a:=WilsonIndependentFittedRelativeClock.reported A O N s (m-s)
  rw [Nat.add_sub_of_le before] at a
  simp_rw [a]
  rw [map_prod]

end YM.Integration.WilsonIndependentFittedProductClock
