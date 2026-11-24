import YM.Integration.WilsonIndependentMatchedOwnHomeBornRaw
import YM.Integration.WilsonIndependentMatchedOwnHomeOrdinaryPin

/-! The Φ-weighted original complete normalized source at its real pin is
exactly the rehomed whole row after the same old-window kinetic reversion.
This comparison is made separately on each actual prior χ ≥ K. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeMeasuredRoster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Mer.Patrol
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentMatchedOwnHomePanel (born)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonIndependentMatchedOwnHomeReportedShell (reading)
open MeasureTheory
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{n e d:ℕ}{E W V:Credit}
variable (R:Realm G (e+1) E)(Q:Fin ((n+1)+1)→SealR G)(φ:Wilt Q)(b:Herit Q)(Φ:Rarity d)(yOut:ℝ)(o:CellR)
local notation "A₀" => R.draws
local notation "O₀" => R.paid
local notation "F₀" => Q 0
local notation "Qₙ" => (fun i:Fin (n+1)=>Q (Fin.succ i))
local notation "φₙ" => (fun i:Fin (n+1)=>φ (Fin.succ i))
local notation "bₙ" => (fun i:Fin (n+1)=>b (Fin.succ i))

def total (t m c older K N l r:ℕ)(w:Fin r→YForest G):ℝ:=
  let ε:=paceT R.draws.S t c
  let y:=paceT R.draws.S m c
  let X:=normalized A₀ O₀ Q b m N
  ∑s∈canvasM Φ ε yOut,ε^4*∫z:CellR,Φ.ψ.val (Mer.address ε yOut o s z.val)*
    (hear R (capP Q) N c older s K (Ashore Q A₀ O₀ φ X m K N y z)).2 l r w ∂dayMeasure

theorem placed (roster:HorizonP H R W V Q)(t m c older K N l r:ℕ)(gate:R.anchor ≤ t)(tm:t ≤ m)(mk:m ≤ K)
    (top:K ≤ N)(before:older ≤ K)(w:Fin r→YForest G):
    let T:=paceT R.draws.S m t
    let Y:=PermuteLens A₀ O₀ F₀ N t (brought A₀ O₀ F₀ N t m (b 0))
    total R Q φ b Φ yOut o t m c older K N l r w=
      (T^(Q 0).h)⁻¹*born R Qₙ F₀ φₙ (scaled (φ 0) T (pace_pos ..)) (normalized A₀ O₀ Qₙ bₙ m N) Y
        Φ yOut o t m c older K N l r w:=by
  intro T Y
  let ε:=paceT R.draws.S t c
  let y:=paceT R.draws.S m c
  let money:=(T^(Q 0).h)⁻¹
  have deg:capP Q=(Q 0).h+capP Qₙ:=by unfold capP asp;exact Fin.sum_univ_succ _
  let value (s:Cover)(z:CellR):ℝ:=(hear R (capP Q) N c older s K
    (Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y z)).2 l r w
  let lower (s:Cover):Lounge:=(WilsonIndependentMatchedOwnHomePanel.landed R Qₙ F₀ φₙ (scaled (φ 0) T (pace_pos ..))
    (normalized A₀ O₀ Qₙ bₙ m N) Y t m c older K N y s).2 l r w
  have tested (s:Cover)(z:CellR):value s z=money*(lower s z):=by
    dsimp only [value];rw [deg]
    exact congrArg (fun B:Era G ℝ=>B.2 l r w)
      (WilsonIndependentMatchedOwnHomeOrdinaryPin.pin R Q φ b roster t m c older K N gate tm mk top before y s z)
  let test (s:Cover)(z:CellR):=Φ.ψ.val (Mer.address ε yOut o s z.val)
  change (∑s∈canvasM Φ ε yOut,ε^4*∫z:CellR,test s z*value s z ∂dayMeasure)=
    money*∑s∈canvasM Φ ε yOut,ε^4*∫z:CellR,test s z*lower s z ∂dayMeasure
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro s _
  calc
    _=ε^4*∫z:CellR,money*(test s z*lower s z) ∂dayMeasure:=by
      apply congrArg (ε^4*·)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z=>by change test s z*value s z=money*(test s z*lower s z);rw [tested s z];ring
    _=_:=by rw [integral_const_mul];ring

def reported (t m c older K N q:ℕ)(g ρ:ℝ)(w:Fin 0→YForest G):ℂ:=
  reading R.draws R.paid N m older q g fun l=>ρ^4*total R Q φ b Φ yOut o t m c older K N l 0 w

theorem original (roster:HorizonP H R W V Q)(t m c older K N q:ℕ)(gate:R.anchor ≤ t)(tm:t ≤ m)(mk:m ≤ K)
    (top:K ≤ N)(before:older ≤ K)(g ρ:ℝ)(w:Fin 0→YForest G):
    let T:=paceT R.draws.S m t
    let Y:=PermuteLens A₀ O₀ F₀ N t (brought A₀ O₀ F₀ N t m (b 0))
    reported R Q φ b Φ yOut o t m c older K N q g ρ w=
      WilsonIndependentMatchedOwnHomeBornRaw.measured R Qₙ F₀ φₙ (scaled (φ 0) T (pace_pos ..)) (normalized A₀ O₀ Qₙ bₙ m N) Y
        Φ yOut o t m c older K N q g ρ w:=by
  intro T Y
  apply congrArg (reading R.draws R.paid N m older q g)
  funext l
  rw [placed R Q φ b Φ yOut o roster t m c older K N l 0 gate tm mk top before w]
  ring
end YM.Integration.WilsonIndependentMatchedOwnHomeMeasuredRoster
end
