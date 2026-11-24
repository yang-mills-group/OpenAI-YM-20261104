import YM.Integration.WilsonIndependentMatchedRosterPowers
import YM.Integration.WilsonIndependentMatchedRosterTariff

/-! A single optical budget pays the entire finite roster. Every occupied
source is restored exactly once and every designated remainder retains its
own quarter-power over the part of the course above its first connection. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterMoney
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterTariff
open WilsonIndependentMatchedRosterPowers
variable {n k u b e:ℕ}

theorem original (C S V:ℝ)(d w:Fin (n+1)→ℕ)(A B:Fin (n+1)→ℝ)(δ x L t z:ℝ)
    (hc:0≤C)(hs:0≤S)(ha:∀s,0≤A s)(hb:∀s,0≤B s)(hx:0<x)(hL:1≤L)(hd:0<δ)(ht:0<t)(hz:0≤z)
    (money:C*S*L^((∑s,d s)+(∑s,w s)) ≤ V):
    let r:=x*L
    C*((n:ℝ)*S*pearlB u b (4*z) (t/r)*nuP (coinMat k e+1) n (fun s=>offer u b (d s) (w s) z δ x (A s) (B s))) ≤ 
      V*profiles n k e u b t z (∏s,factor u b z*(B s*A s))*
        r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4):=by
  let Z:=fun s=>factor u b z*(B s*A s)
  have source:(∏s,offer u b (d s) (w s) z δ x (A s) (B s))=
    (∏s,Z s)*(x^(∑s,d s))⁻¹*(δ/x)^(((∑s,w s:ℕ):ℝ)/4):=by
    calc _ = ∏s,Z s*((x^d s)⁻¹*(δ/x)^((w s:ℝ)/4)):=by
          apply Finset.prod_congr rfl
          intro s _
          unfold offer WilsonIndependentMatchedRosterTariff.weight Z
          ring
         _ = _ := wages Finset.univ d w Z δ x hd hx
  have hpos:0<L:=zero_lt_one.trans_le hL
  have opt:L^(((∑s,w s:ℕ):ℝ)/4) ≤ L^(∑s,w s):=by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL
    have h:0≤(((∑s,w s:ℕ):ℕ):ℝ):=by positivity
    linarith
  have price:C*S*(L^(∑s,d s)*L^(((∑s,w s:ℕ):ℝ)/4))≤V:=by
    rw [pow_add] at money
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left opt (by positivity)) (by positivity)).trans money
  have good:0≤profiles n k e u b t z (∏s,Z s):=by
    have p:0≤∏s,Z s:=Finset.prod_nonneg fun s _=>by have a:=ha s;have c:=hb s;unfold Z WilsonIndependentMatchedRosterTariff.factor;positivity
    have coin:=coinMat_nn k e
    unfold profiles;positivity
  dsimp only
  rw [loadRep,source,bill C S (∑s,d s) (∑s,w s) δ x L t z (∏s,Z s) hx hpos hd ht]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right price good)
    (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)

end YM.Integration.WilsonIndependentMatchedRosterMoney
