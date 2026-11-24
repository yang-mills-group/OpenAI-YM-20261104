import YM.Integration.WilsonSeparatedPrefixMovingPinChamber

/-! Unfold the nominated return at the genuine upper cutoff, before any near or far merger. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedRaw
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingSummedCenter (issued)
open WilsonSeparatedPrefixMovingPinFlow (packet)
open WilsonPositionProgramPinnedHearthHistory (pin)
open WilsonSeparatedPrefixMovingPinProduct (landed)
open WilsonSeparatedPrefixMovingPinCanvas (total)
open WilsonSeparatedPrefixMovingPinSigned (slice)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open Finset MeasureTheory
open scoped BigOperators Topology Classical

variable {G:Gauge}{D e n:ℕ}{E:Credit}



def raw (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(α:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(φ:Rarity D)(y:ℝ)(o:CellR)(t m b older N q r:ℕ)(w:Fin r→YForest G):ℝ:=
  let ε:=paceT R.draws.S t b
  let zNear:=paceT R.draws.S m b
  let here (s:Cover)(z:CellR):=hear R (F.h+capP Q) N b older s N
    (agateV (WilsonSeparatedPrefixMovingPairSector.current R F ψ Y t N N (zNear/paceT R.draws.S m t) z)
      (Ashore Q R.draws R.paid α X m N N zNear z))
  ∑s∈canvasM φ ε y,ε^4*∫z:CellR,φ.ψ.val (Mer.address ε y o s z.val)*(here s z).2 q r w ∂dayMeasure

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)
    (φ:Rarity D)(y:ℝ)(o:CellR)(t m b older N q r:ℕ)(w:Fin r→YForest G)(enrolled:R.anchor≤N)(past:older≤N)(cut:b≤N):
    panel R Q F α ψ X Y φ y o t m b older N N q r w=raw R Q F α ψ X Y φ y o t m b older N q r w:=by
  unfold WilsonSeparatedPrefixMovingPinChamber.panel WilsonSeparatedPrefixMovingPinCanvas.total raw;apply Finset.sum_congr rfl;intro s _
  congr 1;apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
  apply congrArg (fun c:ℝ=>φ.ψ.val (Mer.address (paceT R.draws.S t b) y o s z.val)*c)
  have native:=WilsonSeparatedPrefixMovingPinProduct.original R Q F roster far α ψ X Y s (paceT R.draws.S m b) t m b older N N z enrolled past le_rfl
  rw [(WilsonSeparatedPrefixMovingPinFlow.endpoints R Q F roster α ψ X Y z (paceT R.draws.S m b) t m b N enrolled cut).1] at native
  exact congrArg (fun Z:Era G ℝ=>Z.2 q r w) native

end YM.Integration.WilsonSeparatedPrefixMovingPinnedRaw
