import YM.Integration.WilsonIndependentMatchedOwnHomePanel
import YM.Integration.WilsonIndependentMatchedOwnHomeBasis
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture

/-! Reframe the particular filed, cutoff-dependent complete roster itself:
the near letters keep their old m projection, and the far letter is filed
on its own t, including the scalar and every lower mode, before this same
pin is heard on either the N-vacuum or the K-vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeOrdinaryPin
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Mer.Patrol
open WilsonIndependentSpoutMasterArms (arm)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentMatchedOwnHomeBasis (asking)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonPositionProgramPinnedHearthHistory (pin)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{E W V:Credit}
variable (R:Realm G (e+1) E)(Q:Fin ((n+1)+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
local notation "A₀" => R.draws
local notation "O₀" => R.paid
local notation "F₀" => Q 0
local notation "Qₙ" => (fun i:Fin (n+1)=>Q (Fin.succ i))
local notation "φₙ" => (fun i:Fin (n+1)=>φ (Fin.succ i))
local notation "bₙ" => (fun i:Fin (n+1)=>b (Fin.succ i))

private theorem scale (t:ℝ)(P U:Era G ℝ):agateV (t • P) U=t • agateV P U:=by
  let row:Fin 2→Era G ℝ:=![P,U]
  let money:Fin 2→ℝ:=![t,1]
  have sale:=WilsonIndependentMatchedOwnHomeRoster.real_product row money
  change agateV (t • P) ((1:ℝ) • U)=(∏i,money i) • agateV P U at sale
  simpa only [one_smul,Fin.prod_univ_two,money,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,mul_one] using sale

theorem group (fund:PassportC H R F₀ W V)(t m K N:ℕ)(old:R.anchor ≤ t)(tm:t ≤ m)(mk:m ≤ K)(top:K ≤ N)(y:ℝ)(o:CellR):
    let T:=paceT R.draws.S m t
    Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y o=
      (T^(Q 0).h)⁻¹ • agateV (asking R F₀ (φ 0) (b 0) t m K N y o)
        (Ashore Qₙ A₀ O₀ φₙ (normalized A₀ O₀ Qₙ bₙ m N) m K N y o):=by
  intro T
  change agateV (arm A₀ O₀ (Q 0) (φ 0) (b 0) m K N y o) _=_
  rw [WilsonIndependentMatchedOwnHomeBasis.hearing R (Q 0) fund (φ 0) (b 0) t m K N old tm mk top y o,scale]
  rfl

theorem pin (roster:HorizonP H R W V Q)(t m c older K N:ℕ)(gate:R.anchor ≤ t)(tm:t ≤ m)(mk:m ≤ K)(top:K ≤ N)
    (before:older ≤ K)(y:ℝ)(s:Cover)(z:CellR):
    let T:=paceT R.draws.S m t
    let Y:=PermuteLens A₀ O₀ F₀ N t (brought A₀ O₀ F₀ N t m (b 0))
    let Yₙ:=normalized A₀ O₀ Qₙ bₙ m N
    hear R ((Q 0).h+capP Qₙ) N c older s K (Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y z)=
      (T^(Q 0).h)⁻¹ • locale z (WilsonIndependentMatchedOwnHomePanel.landed R Qₙ F₀ φₙ
        (scaled (φ 0) T (pace_pos ..)) Yₙ Y t m c older K N y s):=by
  intro T Y Yₙ
  let far:PassportC H R F₀ W V:=(roster 0).some
  have smallR:HorizonP H R W V Qₙ:=fun i=>roster i.succ
  have entry:=WilsonIndependentMatchedOwnHomePanel.placed R Qₙ F₀ φₙ (scaled (φ 0) T (pace_pos ..)) Yₙ Y
    smallR far t m c older K N y s z (gate.trans (tm.trans mk)) before top
  rw [entry,group R Q φ b far t m K N gate tm mk top y z]
  let P:=agateV (asking R F₀ (φ 0) (b 0) t m K N y z) (Ashore Qₙ A₀ O₀ φₙ Yₙ m K N y z)
  let cash:=(T^(Q 0).h)⁻¹
  have actual:Auth (Q 0).h (asking R F₀ (φ 0) (b 0) t m K N y z):=
    locale_val _ (passportHead far _ _ _ (gate.trans (tm.trans mk)) top) z
  have legit:Auth ((Q 0).h+capP Qₙ) P:=actual.manor (ash_head smallR _ _ (gate.trans (tm.trans mk)) top z)
  let off:=WilsonPositionProgramPinnedHearthHistory.pin R.draws.S c K s
  change cruises A₀ O₀ N _ K older (cash • shifted P off)=cash • cruises A₀ O₀ N _ K older (shifted P off)
  exact WilsonSeparatedPrefixMovingFixedCapture.settled R (legit.shifted off) cash before top
end YM.Integration.WilsonIndependentMatchedOwnHomeOrdinaryPin
end
