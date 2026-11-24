import YM.Integration.WilsonIndependentMatchedCoverJoined
import YM.WilsonCoeffUV.Product.Connected.FirstJoin

/-! The exterior meets a product of still separate near fields on their common
normalized Mer history. Only the distances from that exterior enter its crossing
price. Each near field keeps its own root and its already deposited scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCohorts
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{k e u b i c N m n l:ℕ}{E W:Credit}

/-- The native conditional mixed field and the entire unjoined product of
conditional means on the same board. The old scalar is present in both. -/
theorem crossing (R:Realm G (e+1) E)(sale:SpringD R k u b W)
    (live:R.anchor ≤ i)(edge:i < c)(top:c ≤ N)
    (P:Era G ℝ)(Q:Fin (n+1)→Era G ℝ)(h:Fin (n+1)→ℕ)(room:l + (∑ j, h j) ≤ k)
    (front:ProfileW)(roots:Fin (n+1)→ProfileW)(η K D A:ℝ)(B:Fin (n+1)→ℝ)
    (separate:∀j,SplitHill front (roots j) η K D)
    (exterior:Income P l e (u+b) (heirP R.draws i front) A)
    (nearby:∀j,Income (Q j) (h j) e (u+b) (heirP R.draws i (roots j)) (B j)):
    let near:=MassP G ℝ n Q
    let j:=∑v,h v
    let born:=JoinGap R.draws R.paid i N l j P near
    verseI R.draws R.paid i N (l+j) (agateV P near)=
        born+agateV (verseI R.draws R.paid i N l P) (verseI R.draws R.paid i N j near) ∧
      Auth (l+j) born ∧ Flush e u η born
        (R.cash (priceWG G e k u b E W) i*(pearlB u b K D*(A*nuP (coinMat k e) n B))) :=by
  dsimp only
  obtain ⟨joint,apart,under⟩:=closingW n front roots separate
  let δ:=max (0:ℝ) (δWarm R i c)
  have nonneg:0≤δ:=le_max_left _ _
  have grouped:=manCo Q h (fun j=>(nearby j).1)
  have prices:PaidMer e (u+b) (heirP R.draws i joint) (MassP G ℝ n Q) (MassP G ℝ n Q)
      (nuP (coinMat k e) n B) δ:=
    pedig n Q Q h B _ (by omega) (fun j=>(nearby j).1) (fun j=>(nearby j).1)
      (fun j=>((nearby j).2 δ nonneg).grade (fun x=>under j _) le_rfl) nonneg
  have grant:=enterShore sale live edge top top P P (MassP G ℝ n Q) (MassP G ℝ n Q)
    exterior.1 exterior.1 grouped grouped apart room (le_max_right 0 _) (exterior.2 δ nonneg) prices
  exact ⟨(sub_add_cancel _ _).symm,grant.pen,grant.f_l⟩

/-- The projected scalar at the stipulated older date pays the same crossing
factor as its whole connected field. This uses the actual earlier normalized
Mer steps, including the scalar feeds from every positive rank. -/
theorem older (G:Gauge)(l j e u:ℕ)(E L:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E),Dormitory R (l+j) u L →
      ∀ m i N, ∀(η:ℕ→ℝ)(Z:ℝ),Escort R m i η → PadRank R m i Z → i<N →
      ∀P Q:Era G ℝ,let born:=JoinGap R.draws R.paid i N l j P Q
        ∀wage:ℝ, Auth (l+j) born → Flush e u (η i) born wage →
          let arrived:=cruises R.draws R.paid N (l+j) i m born
          Flush e u (η m) arrived (C.buy Z*wage) ∧
          ∀grade≤e,∀q:Fin 0→YForest G,‖arrived.2 grade 0 q‖≤C.buy Z*wage:=by
  obtain ⟨C,carry⟩:=waveSeen G (l+j) e u E L
  refine ⟨C,?_⟩
  intro R grant m i N η Z route budget age P Q born wage auth paid
  let δ:=max (0:ℝ) (R.tempC i i)
  have receipt:=(carry R grant m i η i N N _ δ Z route budget le_rfl age.le age.le
    (le_max_right _ _) _ _ (Fringed.same paid auth (le_max_left _ _))).f_l
  exact ⟨receipt,fun grade hg=>WilsonIndependentMatchedCoverJoined.unit receipt grade hg⟩

end YM.Integration.WilsonSeparatedPrefixMovingCohorts
