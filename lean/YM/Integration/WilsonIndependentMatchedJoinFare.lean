import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! One separated two-source birth on its real parent mesh. Each designated
weight is retained before the spatial charges and the fixed coarse ratio are paid. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedJoinFare
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

private lemma mesh (l r b:ℕ)(x L:ℝ)(hx:0<x)(hL:0<L):
    ((x^l)⁻¹*(x^r)⁻¹)*(x*L)^b=L^(l+r)*(x*L)^((b:ℝ)-((l+r:ℕ):ℝ)) :=by
  rw [Real.rpow_sub (mul_pos hx hL),Real.rpow_natCast,Real.rpow_natCast,mul_pow x L (l+r)]
  rw [pow_add x]
  field_simp [hx.ne',hL.ne']

private lemma gain (δ x L α β:ℝ)(hd:0<δ)(hx:0<x)(hL:0<L):
    (δ/x)^α*(δ/x)^β=L^(α+β)*(δ/(x*L))^(α+β):=by
  rw [←Real.rpow_add (div_pos hd hx),←Real.mul_rpow hL.le (div_nonneg hd.le (mul_nonneg hx.le hL.le))]
  congr 1
  field_simp [hx.ne',hL.ne']

def rent (l r u b:ℕ)(L t z r₁ r₂ α β A B C D:ℝ):ℝ:=
   (t^b)⁻¹*(16*z)^u*((5*r₁)^4*(5*r₂)^4)*
     ((9^(u+b):ℝ)*(9^(u+b):ℝ))*(A*B*C*D)*(L^(l+r)*L^(α+β))

/-- This is an equality for the signed born field's positive fee, including
both positional amplitudes at the actual inner mesh. -/
theorem original {D D':ℕ}(φ:Rarity D)(ψ:Rarity D')(l r u b:ℕ)
    (x y L δ t z α β A B C D₀:ℝ)(hx:0<x)(hL:0<L)(hd:0<δ):
    pearlB u b (4*z) (t/(x*L))*
      (WilsonIndependentMatchedCoverProfile.charge φ (u+b) l x y (A*(δ/x)^α) B*
       WilsonIndependentMatchedCoverProfile.charge ψ (u+b) r x y (C*(δ/x)^β) D₀)=
     rent l r u b L t z (radiusH φ x y) (radiusH ψ x y) α β A B C D₀*
       (x*L)^((b:ℝ)-((l+r:ℕ):ℝ))*(δ/(x*L))^(α+β) :=by
  have peer:pearlB u b (4*z) (t/(x*L))=(t^b)⁻¹*(x*L)^b*(16*z)^u:=by
    unfold pearlB
    rw [← inv_pow,inv_div,div_pow,div_eq_mul_inv]
    ring
  rw [peer]
  unfold WilsonIndependentMatchedCoverProfile.charge BasePrice rent
  calc
    _ = (t^b)⁻¹*(16*z)^u*((5*radiusH φ x y)^4*(5*radiusH ψ x y)^4)*
          ((9^(u+b):ℝ)*(9^(u+b):ℝ))*(A*B*C*D₀)*
          (((x^l)⁻¹*(x^r)⁻¹)*(x*L)^b)*((δ/x)^α*(δ/x)^β) := by ring
    _ = _ :=by rw [mesh l r b x L hx hL,gain δ x L α β hd hx hL]; ring

end YM.Integration.WilsonIndependentMatchedJoinFare
