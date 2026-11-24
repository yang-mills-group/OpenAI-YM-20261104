import YM.Integration.WilsonIndependentMatchedRosterTariff
import YM.Integration.WilsonIndependentMatchedRosterChronology

/-! The complete product of means survives the formation sum. Its original
rank zero and all protected lower moments stay on the same report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterHome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterChronology (mass)
open WilsonIndependentMatchedRosterTariff (factor offer)
variable {G:Gauge}{n e u b:ℕ}{E:Credit}{D:Fin (n+1)→ℕ}

theorem original (R:Realm G (e+1) E)(m h N:ℕ)(d w l:Fin (n+1)→ℕ)
    (φ:(s:Fin (n+1))→Rarity (D s))(P:Fin (n+1)→ℕ→Era G ℝ)
    (δ y z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ)(hd:0<δ)(cap:∀s,radiusH (φ s) 1 y≤z)
    (cash:∀s,0≤A s)(test:∀s,Amplitude (φ s) (B s))
    (lane:∀s,Lane R (l s) (d s) m h N u b (φ s) y o δ ((w s:ℝ)/4) (A s) (B s) (P s)):
    let Z:=∏s,factor u b z*(B s*A s)
    Auth (∑s,l s) (mass P 0) ∧ Flush e u 1 (mass P 0)
      ((coinMat (∑s,l s) e)^n*Z * δ^(((∑s,w s:ℕ):ℝ)/4)):=by
  let Z:=fun s=>factor u b z*(B s*A s)
  let pay:=fun s=>Z s*δ^((w s:ℝ)/4)
  have each (s):Fringed (l s) e u 1 (pay s) 0 (P s 0) (P s 0):=by
    have raw:=(lane s).accounts.home
    have a:=WilsonIndependentMatchedRosterTariff.outgoing (φ s) u b (d s) (w s) δ 1 1 y z (A s) (B s) zero_lt_one le_rfl hd
      (cash s) (test s).1 (cap s)
    have inc:WilsonIndependentMatchedCoverHome.bill (φ s) u (d s) y (A s*δ^((w s:ℝ)/4)) (B s) ≤ pay s:=by
      simpa only [WilsonIndependentMatchedRosterLane.chargeBelow,WilsonIndependentMatchedCoverHome.bill,
        offer,WilsonIndependentMatchedRosterTariff.weight,BasePrice,one_pow,inv_one,one_mul,div_one,pay,Z,mul_assoc] using a
    exact Fringed.same ⟨raw.1.trans inc,fun j hj k hk=>(raw.2 j hj k hk).more inc⟩
      ((lane s).accounts.head 0 (Nat.zero_le _)) le_rfl
  have all:=valueP n (fun s=>P s 0) (fun s=>P s 0) l pay (k:=∑s,l s) le_rfl each zero_le_one
  have fee:nuP (coinMat (∑s,l s) e) n pay=
      (coinMat (∑s,l s) e)^n*(∏s,Z s)*δ^(((∑s,w s:ℕ):ℝ)/4):=by
    rw [loadRep]
    simp only [pay,Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hd,←Finset.sum_div,←Nat.cast_sum]
    ring
  exact ⟨all.pen,fee ▸ all.f_l⟩

end YM.Integration.WilsonIndependentMatchedRosterHome
