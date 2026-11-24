import YM.Integration.WilsonIndependentMatchedCoverProfile
import YM.WilsonCoeffUV.Product.Report.Layout

/-! The first connected birth after two located insertions on the same
cover program. Both old scalars are kept in the ordinary product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverCrossing
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{D D' k i j e u b m c N:ℕ}{E W:Credit}

theorem original (R:Realm G (e+1) E)(sale:SpringD R k u b W)
    (live:R.anchor≤m)(earlier:m<c)(above:c≤N)(room:i+j≤k)
    {φ:Rarity D}{ψ:Rarity D'}(P Q:Era G ℝ)(x y t z:ℝ)(o:CellR)
    (mesh:0<x)(fits:x*(ll R.draws m).L.val≤1)(sep:ClearDay φ ψ t)(hsep:0<t)
    (φfits:radiusH φ (x*(ll R.draws m).L.val) y≤z)
    (ψfits:radiusH ψ (x*(ll R.draws m).L.val) y≤z)
    (lp:(VisitsT φ x y o).Nonempty)(rp:(VisitsT ψ x y o).Nonempty)
    {A B:ℝ}(left:Income P i e (u+b) (OrbP (ll R.draws m) φ x y o) A)
    (right:Income Q j e (u+b) (OrbP (ll R.draws m) ψ x y o) B):
    let η:=x*(ll R.draws m).L.val
    let connected:= JoinGap R.draws R.paid m N i j P Q
    verseI R.draws R.paid m N (i+j) (agateV P Q) =
      connected+agateV (verseI R.draws R.paid m N i P) (verseI R.draws R.paid m N j Q) ∧
    Flush e u η connected
      (R.cash (priceWG G e k u b E W) m*(pearlB u b (4*z) (t/η)*(A*B))) := by
  dsimp only
  refine ⟨(sub_add_cancel _ _).symm,?_⟩
  let δ:=max (0:ℝ) (δWarm R m c)
  have f:=disjointly (ll R.draws m) φ ψ x y t z o mesh fits sep hsep φfits ψfits lp rp
  exact (enterShore sale live earlier above above P P Q Q left.1 left.1 right.1 right.1 f
    room (le_max_right 0 _) (left.2 δ (le_max_left _ _)) (right.2 δ (le_max_left _ _))).f_l

end YM.Integration.WilsonIndependentMatchedCoverCrossing
