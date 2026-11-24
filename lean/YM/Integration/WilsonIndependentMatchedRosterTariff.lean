import YM.Integration.WilsonIndependentMatchedRosterLane

/-! Each actual field pays its own incoming engineering power and
designated stable gain. A fixed shape/derivative constant pays its two
different native fine and coarse tests at the same original Wilson edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterTariff
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (chargeBelow)

def factor (u b:ℕ)(z:ℝ):ℝ:=(5*z)^4*((9:ℝ)^(u+b)+(1+4*z)^u)
def weight (d w:ℕ)(δ x A B:ℝ):ℝ:=(x^d)⁻¹*(B*A)*(δ/x)^((w:ℝ)/4)
def offer (u b d w:ℕ)(z δ x A B:ℝ):ℝ:=factor u b z*weight d w δ x A B

lemma positive (u b d w:ℕ){z δ x A B:ℝ}(hz:0≤z)(hδ:0≤δ)(hx:0≤x)(ha:0≤A)(hb:0≤B):
    0≤offer u b d w z δ x A B:=by unfold offer factor weight;positivity

variable {D:ℕ}
theorem incoming (φ:Rarity D)(u b d w:ℕ)(δ x y z A B:ℝ)(hx:0<x)(hd:0<δ)
    (ha:0≤A)(hb:0≤B)(cap:radiusH φ x y≤z):
    charge φ (u+b) d x y (A*(δ/x)^((w:ℝ)/4)) B ≤offer u b d w z δ x A B:=by
  have radius:0≤radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  have crown:0≤z:=radius.trans cap
  have growing:(5*radiusH φ x y)^4*((9:ℝ)^(u+b)) ≤ factor u b z:=by
    unfold factor
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) _ (by positivity) (by positivity)
    exact le_add_of_nonneg_right (by positivity)
  have whole:0≤weight d w δ x A B:=by unfold weight;positivity
  calc
    _ = ((5*radiusH φ x y)^4*((9:ℝ)^(u+b)))*weight d w δ x A B:=by unfold WilsonIndependentMatchedCoverProfile.charge BasePrice weight;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right growing whole

theorem outgoing (φ:Rarity D)(u b d w:ℕ)(δ x r y z A B:ℝ)(hx:0<x)(hr:x≤r)(hd:0<δ)
    (ha:0≤A)(hb:0≤B)(cap:radiusH φ r y≤z):
    chargeBelow φ u d r y (A*(δ/r)^((w:ℝ)/4)) B ≤offer u b d w z δ x A B:=by
  have gr:0<r:=hx.trans_le hr
  have radius:0≤radiusH φ r y:=zero_le_one.trans (fieldCap ..)
  have crown:0≤z:=radius.trans cap
  have grows:(5*radiusH φ r y)^4*(1+4*radiusH φ r y)^u≤factor u b z:=by
    unfold factor
    have h₁:(5*radiusH φ r y)^4≤(5*z)^4:=pow_le_pow_left₀ (by positivity) (by linarith) _
    have h₂:(1+4*radiusH φ r y)^u≤(1+4*z)^u:=pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mul_le_mul h₁ (h₂.trans (le_add_of_nonneg_left (by positivity))) (by positivity) (by positivity)
  have lev:0≤(5*z)^4*((9:ℝ)^(u+b)+(1+4*z)^u):=by positivity
  have h₁:(r^d)⁻¹≤(x^d)⁻¹:=inv_anti₀ (pow_pos hx _) (pow_le_pow_left₀ hx.le hr _)
  have h₂:(δ/r)^((w:ℝ)/4)≤(δ/x)^((w:ℝ)/4):=Real.rpow_le_rpow (by positivity)
    (div_le_div_of_nonneg_left hd.le hx hr) (by positivity)
  have wage:weight d w δ r A B≤weight d w δ x A B:=by
    unfold weight
    exact mul_le_mul (mul_le_mul_of_nonneg_right h₁ (by positivity)) h₂ (by positivity) (by positivity)
  calc
    _=((5*radiusH φ r y)^4*(1+4*radiusH φ r y)^u)*weight d w δ r A B:=by
      unfold chargeBelow BasePrice weight;ring
    _ ≤ _ := mul_le_mul grows wage (by unfold weight;positivity) lev

end YM.Integration.WilsonIndependentMatchedRosterTariff
