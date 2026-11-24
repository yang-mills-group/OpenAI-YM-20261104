import YM.Integration.WilsonIndependentMovingRosterStableSale
import YM.Integration.WilsonIndependentMovingRosterStableLedger

/-! The genuine product of all the single-source returns at the common near
report, with the exterior still normalized at its own report. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableLanding

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterStableMoney (fees)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n e u b:ℕ}{D:Fin ((n+1)+1)→ℕ}{E:Credit}

theorem original (R:Realm G (e+1) E)(t m N:ℕ)(away:t ≤ m)(upper:m ≤ N)
    (l d w:Fin ((n+1)+1)→ℕ)(φ:(s:Fin ((n+1)+1))→Rarity (D s))
    (P:Fin ((n+1)+1)→ℕ→Era G ℝ)(A B:Fin ((n+1)+1)→ℝ)(y z:ℝ)(o:CellR):
    let T:=paceT R.draws.S m t
    let δ:=paceT R.draws.S m N
    let Y:=fun s=>P s (m-homes t m s)
    1≤T → (∀s,0≤A s) → (∀s,Amplitude (φ s) (B s)) →
    (∀s,radiusH (φ s) 1 (centers y T s)≤z) →
    (∀s,Lane R (l s) (d s) (homes t m s) (N-homes t m s) N u b (φ s) (centers y T s) o
      (paceT R.draws.S (homes t m s) N) ((w s:ℝ)/4) (A s) (B s) (P s)) →
    Auth (∑s,l s) (MassP G ℝ (n+1) Y) ∧ Flush e u 1 (MassP G ℝ (n+1) Y)
      (T^(d 0+u)*((coinMat (∑s,l s) e)^(n+1)*(∏s,factor u b z*(B s*A s))*
       δ^(((∑s,w s:ℕ):ℝ)/4))):=by
  intro T δ Y zoom paid tests caps lanes
  let pay:=fees u b d w A B z δ 1 T
  let amount:=Fin.cons (α:=fun _=>ℝ) (T^u*pay 0) (Fin.tail pay)
  have schedule (i:ℕ):paceT R.draws.S t i=paceT R.draws.S m i/T:=
    WilsonSeparatedPrefixMovingUnformed.rulers _ _ _ _
  have records (s):Auth (l s) (Y s) ∧
      Flush e u (Fin.cons (α:=fun _=>ℝ) (1/T) (fun _:Fin (n+1)=>1) s) (Y s) (pay s):=by
    have site:homes t m s ≤ m:=Fin.cases away (fun _=>le_rfl) s
    have raw:=WilsonIndependentMovingRosterStableLedger.resident R (l s) (d s) (w s) u b (homes t m s)
      m N site upper (φ s) (centers y T s) z o _ (A s) (B s) (P s) (pace_pos ..)
      (paid s) (tests s) (caps s) (lanes s)
    refine ⟨raw.1,?_⟩
    have angular:=raw.2
    induction s using Fin.cases with
    | zero=>simpa only [pay,fees,homes,Fin.cons_zero,Y,schedule,pace_self] using angular
    | succ s=>simpa only [pay,fees,homes,Fin.cons_succ,Y,pace_self] using angular
  have each (s):Fringed (l s) e u 1 (amount s) 0 (Y s) (Y s):=by
    apply Fringed.same _ (records s).1 le_rfl
    induction s using Fin.cases with
    | zero=>exact WilsonIndependentMovingRosterStableEdge.ruler zero_le_one zoom (records 0).2
    | succ s=>exact (records s.succ).2
  have result:=valueP (n+1) Y Y l amount (k:=∑s,l s) le_rfl each zero_le_one
  have counted:=WilsonIndependentMovingRosterStableLedger.units u b d w A B δ T z
    (coinMat (∑s,l s) e) zoom (pace_pos ..)
  exact ⟨result.pen,counted ▸ result.f_l⟩

end YM.Integration.WilsonIndependentMovingRosterStableLanding
