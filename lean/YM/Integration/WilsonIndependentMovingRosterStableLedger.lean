import YM.Integration.WilsonIndependentMovingRosterStableMoney
import YM.Integration.WilsonIndependentMovingRosterStableEdge
import YM.Integration.WilsonIndependentMovingRosterLaneEdge

/-! A bought stable or fitted lane can be read at an absolute intermediate
date, including its finest or its own reporting date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableLedger

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer weight factor)
open WilsonIndependentMovingRosterStableMoney (fees)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n D e:ℕ}{E:Credit}

theorem resident (R:Realm G (e+1) E)(l d w u b home j N:ℕ)(start:home≤j)(top:j≤N)
    (φ:Rarity D)(y z:ℝ)(o:CellR)(δ A B:ℝ)(P:ℕ→Era G ℝ)(dp:0<δ)(ap:0≤A)
    (test:Amplitude φ B)(box:radiusH φ 1 y≤z)
    (funded:Lane R l d home (N-home) N u b φ y o δ ((w:ℝ)/4) A B P):
    let x:=paceT R.draws.S home j
    Auth l (P (j-home)) ∧ Flush e u x (P (j-home)) (offer u b d w z δ x A B):=by
  intro x
  have legal:j-home≤N-home:=Nat.sub_le_sub_right top home
  have x₀:0<x:=pace_pos ..
  have xc:x≤1:=pace_le _ start
  have box₀:0≤z:=(zero_le_one.trans (fieldCap ..)).trans box
  have heard:=funded.billed (j-home) legal
  rw [Nat.add_sub_of_le start] at heard
  have cost:=WilsonIndependentMatchedRosterTariff.outgoing φ u b d w δ x x y z A B x₀ le_rfl
    dp ap test.1 (WilsonIndependentMatchedRosterDate.radius _ x₀ xc box)
  exact ⟨funded.accounts.head _ legal,WilsonIndependentMatchedRosterTariff.positive _ _ _ _ box₀ dp.le x₀.le ap test.1,
    fun q hq r hr=>(heard.2 q hq r hr).more cost⟩

theorem units (u b:ℕ)(d w:Fin ((n+1)+1)→ℕ)(A B:Fin ((n+1)+1)→ℝ)(δ T z C:ℝ)
    (zoom:1≤T)(vp:0<δ):
    let a:=fees u b d w A B z δ 1 T
    let amount:=Fin.cons (α:=fun _=>ℝ) (T^u*a 0) (Fin.tail a)
    nuP C (n+1) amount = T^(d 0+u)*(C^(n+1)*(∏s,factor u b z*(B s*A s))*
      δ^(((∑s,w s:ℕ):ℝ)/4)):=by
  intro a amount
  let dollars:=fun s=>offer u b (d s) (w s) z δ 1 (A s) (B s)
  have fare:a 0=T^(d 0)*dollars 0:=
    WilsonIndependentMovingRosterStableMoney.charge u b (d 0) (w 0) z δ 1 T (A 0) (B 0) zoom
  have tail:Fin.tail amount=Fin.tail dollars:=by funext s;rfl
  have head:amount 0=T^u*(T^(d 0)*dollars 0):=by change T^u*a 0=_;rw [fare]
  have raised:nuP C (n+1) amount=T^(d 0+u)*nuP C (n+1) dollars:=by
    rw [nuP,nuP,tail,head,pow_add];ring
  have portions (s):dollars s=(factor u b z*(B s*A s))*δ^(((w s:ℕ):ℝ)/4):=by
    simp only [dollars,offer,WilsonIndependentMatchedRosterTariff.weight,one_pow,inv_one,one_mul,div_one]
    ring
  rw [raised,loadRep];simp_rw [portions]
  rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos vp,←Finset.sum_div,←Nat.cast_sum]
  ring

end YM.Integration.WilsonIndependentMovingRosterStableLedger
