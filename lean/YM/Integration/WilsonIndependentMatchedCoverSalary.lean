import YM.Integration.WilsonIndependentMatchedCoverCap

/-! After the actual per-date earning, one fixed geometric test and source bill
remains. It uses each genuine occupied source dose exactly once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverSalary
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoverDate
variable {G:Gauge}{D D' e:ℕ}{E:Credit}

def profile (u b:ℕ)(t z s₁ s₂ A B C D₀:ℝ):ℝ:=
  (t^b)⁻¹*(16*z)^u*((5*s₁)^4*(5*s₂)^4)*
    ((9^(u+b):ℝ)*(9^(u+b):ℝ))*(A*B*C*D₀)

lemma nonneg (u b:ℕ){t z s₁ s₂ A B C D₀:ℝ}(ht:0 ≤ t)(hz:0 ≤ z)
    (hA:0 ≤ A)(hB:0 ≤ B)(hC:0 ≤ C)(hD:0 ≤ D₀):
    0 ≤ profile u b t z s₁ s₂ A B C D₀:=by unfold profile;positivity

theorem original (C W:Credit)(R:Realm G (e+1) E)(l r k u b m i:ℕ)
    (φ:Rarity D)(ψ:Rarity D')(y t z α β A B C₁ D₁ V:ℝ)
    (x:ℝ)(mesh:x=paceT R.draws.S m (i+1))(hx:0<x)(hx':x ≤ 1)
    (ht:0 ≤ t)(hV:0 ≤ V)(hA:0 ≤ A)(hB:0 ≤ B)(hC:0 ≤ C₁)(hD:0 ≤ D₁)
    (hp:radiusH φ 1 y ≤ z)(hq:radiusH ψ 1 y ≤ z)
    (money:let len:ℝ:=(ll R.draws i).L.val
      C.buy (WilsonIndependentMatchedCoverDate.age R m i)*R.cash (priceWG G e k u b E W) i*
        (len^(l+r)*len^(α+β)) ≤ V):
    salary C W R l r k u b m i φ ψ y t z α β A B C₁ D₁ ≤
      V*profile u b t z z z A B C₁ D₁:=by
  let len:ℝ:=(ll R.draws i).L.val
  let M:=C.buy (WilsonIndependentMatchedCoverDate.age R m i)*R.cash (priceWG G e k u b E W) i*
    (len^(l+r)*len^(α+β))
  have lp:0 ≤ len:=by dsimp only [len];positivity
  have hcap:∀{s:ℕ}(Φ:Rarity s),radiusH Φ x y ≤ radiusH Φ 1 y:=by
    intro s Φ;unfold radiusH;rw [abs_of_pos hx,abs_one];linarith
  have left:radiusH φ x y ≤ z:=(hcap φ).trans hp
  have right:radiusH ψ x y ≤ z:=(hcap ψ).trans hq
  have rz:0 ≤ z:=zero_le_one.trans ((fieldCap φ 1 y).trans hp)
  have a₁:0 ≤ radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  have a₂:0 ≤ radiusH ψ x y:=zero_le_one.trans (fieldCap ..)
  have fields:profile u b t z (radiusH φ x y) (radiusH ψ x y) A B C₁ D₁ ≤
      profile u b t z z z A B C₁ D₁:=by
    unfold profile;gcongr
  calc
    _=M*profile u b t z (radiusH φ x y) (radiusH ψ x y) A B C₁ D₁:=by
      unfold salary WilsonIndependentMatchedJoinFare.rent M profile
      rw [mesh];dsimp [len];ring
    _ ≤ _:=mul_le_mul money fields (nonneg u b ht rz hA hB hC hD) hV

end YM.Integration.WilsonIndependentMatchedCoverSalary
