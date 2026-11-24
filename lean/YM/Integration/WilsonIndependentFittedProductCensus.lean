import YM.Integration.WilsonIndependentFittedProductClock

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedProductCensus
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedReportedFilm (funded)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}

private def first (Q:Era G ℝ):Era G ℝ→+Era G ℝ where
  toFun P:=agateV P Q
  map_zero':=Prod.ext (funext fun _=>(woadNull _).2) (woadNull _).2
  map_add' P Z:=(WilsonIndependentMatchedTotalTop.binary P Z Q).1
private def last (P:Era G ℝ):Era G ℝ→+Era G ℝ where
  toFun Q:=agateV P Q
  map_zero':=Prod.ext (funext fun _=>(woadNull _).1) (woadNull _).1
  map_add' Q Z:=(WilsonIndependentMatchedTotalTop.binary Q Z P).2

theorem choices (n:ℕ)(I:Fin (n+1)→Type)[∀j,Fintype (I j)](P:(j:Fin (n+1))→I j→Era G ℝ):
    MassP G ℝ n (fun j=>∑s,P j s)=∑w:(j:Fin (n+1))→I j,MassP G ℝ n (fun j=>P j (w j)):=by
  induction n with
  | zero=>
    letI : Unique (Fin (0+1)):=⟨⟨0⟩,fun i=>Fin.ext (by have:=i.isLt;omega)⟩
    change ∑s,P 0 s=∑w:(j:Fin 1)→I j,P 0 (w 0)
    exact (Equiv.sum_comp (Equiv.piUnique I) (P 0)).symm
  | succ n ih=>
    let tail:Fin (n+1)→Type:=fun j=>I j.succ
    letI : (j:Fin (n+1))→Fintype (tail j):=fun j=>inferInstanceAs (Fintype (I j.succ))
    let Q:=(fun w:(j:Fin (n+1))→tail j=>MassP G ℝ n (fun j=>P j.succ (w j)))
    have expand:=ih tail (fun j=>P j.succ)
    calc
      _ = (first (∑w,Q w)) (∑a,P 0 a):=by
        change agateV _ (MassP G ℝ n (fun j=>∑s,P j.succ s))=_
        change MassP G ℝ n (fun j=>∑s,P j.succ s)=∑w:(j:Fin (n+1))→tail j,MassP G ℝ n (fun j=>P j.succ (w j)) at expand
        rw [expand]
        rfl
      _ = ∑a:I 0,∑w:(j:Fin (n+1))→tail j,agateV (P 0 a) (Q w):=by
        rw [map_sum]
        exact sum_congr rfl (fun a _=>map_sum (last (P 0 a)) Q univ)
      _ = _:=by
        conv_rhs => rw [←Equiv.sum_comp (Fin.consEquiv I),Fintype.sum_prod_type]
        rfl

theorem stopped (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N m i s:ℕ)(before:s≤ m)(endN:m+i≤N)(n:ℕ)(l:Fin (n+1)→ℕ)
    (I:Fin (n+1)→Type)[∀j,Fintype (I j)]
    (c:(j:Fin (n+1))→I j→ Cost)(P Q:(j:Fin (n+1))→I j→Era G ℝ)
    (high:∀j t,Auth (l j) (P j t))(low:∀j t,Auth (l j) (Q j t))
    (filed:∀j t,P j t=funded (reel (relativeC A O N m i) (c j t)) (Q j t))
    (r:ℕ)(x:Fin r→YForest G):
    reading (cruises A O N (∑j,l j) (m+i) s (MassP G ℝ n (fun j=>∑t,P j t))).2 x=
      ∑w:(j:Fin (n+1))→I j,(∏j,clock A O N m s (c j (w j)))*
        reading (cruises A O N (∑j,l j) (m+i) s (MassP G ℝ n (fun j=>Q j (w j)))).2 x:=by
  let top:=fun (w:(j:Fin (n+1))→I j)=>MassP G ℝ n (fun j=>P j (w j))
  have linear:=WilsonIndependentCollarWeightedCruise.original A O simple localO
    (before.trans (Nat.le_add_right m i)) endN univ (fun _=>1) top
    (fun w _=>manCo _ l (fun j=>high j (w j)))
  rw [choices]
  simp only [one_smul] at linear
  rw [linear]
  have joined (f:((j:Fin (n+1))→I j)→Era G ℝ):reading (∑w,f w).2 x=∑w,reading (f w).2 x:=by
    apply PowerSeries.ext
    intro k
    simp [WilsonOlderFreshSoftSocketKinetic.reading,Prod.snd_sum,Finset.sum_apply]
  rw [joined]
  exact sum_congr rfl fun w _=>WilsonIndependentFittedProductClock.applied A O simple localO N m i s before endN
    n l (fun j=>c j (w j)) (fun j=>P j (w j)) (fun j=>Q j (w j))
    (fun j=>high j (w j)) (fun j=>low j (w j)) (fun j=>filed j (w j)) r x

end YM.Integration.WilsonIndependentFittedProductCensus
