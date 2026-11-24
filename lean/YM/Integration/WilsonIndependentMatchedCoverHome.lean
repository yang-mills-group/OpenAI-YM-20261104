import YM.Integration.WilsonIndependentMatchedCoverDate

/-! The still-disconnected product at its own reporting scale includes every
rank and unit. Its moment is bought on each true field before translation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverHome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{D D' k l r e u:ℕ}

def bill (φ:Rarity D)(u l:ℕ)(y A B:ℝ):ℝ:=
  BasePrice l φ 1 y*((1+4*radiusH φ 1 y)^u*(B*A))

theorem placed (P:TowerS G D)(onP:On l P)(φ:Rarity D)(y:ℝ)(o:CellR)(d:ℕ)
    (A B:ℝ)(hφ:Amplitude φ B)(hp:∀j ≤ e,∀k,Fruit 0 1 u (P.2 j k) A):
    Fringed l e u 1 (bill φ u d y A B) 0 (word P φ 1 y o d) (word P φ 1 y o d):=
  census_br P P φ 1 y onP onP o u zero_lt_one le_rfl hφ
    (fun j hj k=>YieldP.same (hp j hj k) le_rfl) le_rfl d

theorem original (P:TowerS G D)(Q:TowerS G D')(onP:On l P)(onQ:On r Q)
    (φ:Rarity D)(ψ:Rarity D')(y:ℝ)(o:CellR)(d₁ d₂:ℕ)(A B C D₀:ℝ)
    (hφ:Amplitude φ B)(hψ:Amplitude ψ D₀)
    (hp:∀j ≤ e,∀k,Fruit 0 1 u (P.2 j k) A)(hq:∀j ≤ e,∀k,Fruit 0 1 u (Q.2 j k) C):
    let both:=agateV (word P φ 1 y o d₁) (word Q ψ 1 y o d₂)
    Auth (l+r) both ∧ Flush e u 1 both
      (coinMat (l+r) e * bill φ u d₁ y A B * bill ψ u d₂ y C D₀):=by
  have left:=placed P onP φ y o d₁ A B hφ hp
  have right:=placed Q onQ ψ y o d₂ C D₀ hψ hq
  exact ⟨left.pen.manor right.pen,(fringedMat left right zero_le_one le_rfl).f_l⟩

end YM.Integration.WilsonIndependentMatchedCoverHome
