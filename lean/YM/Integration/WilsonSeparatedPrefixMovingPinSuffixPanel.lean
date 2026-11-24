import YM.Integration.WilsonSeparatedPrefixMovingPinChamber
import YM.Integration.WilsonSeparatedPrefixMovingPinCanvas
import YM.Integration.WilsonSeparatedPrefixMovingPinBefore

/-! The genuine translated ultraviolet roster and the older chamber in one signed quadrature. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinSuffixPanel
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
open Finset MeasureTheory
open scoped BigOperators Topology Classical

variable {G:Gauge}{D e n:ℕ}{E:Credit}


open WilsonSeparatedPrefixMovingPinChamber (panel)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(α:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(φ:Rarity D)(y:ℝ)(o:CellR)(t m b older N K target:ℕ)(ω:Fin 0→YForest G)
    (enrolled:R.anchor≤K)(past:older≤K)(cut:K≤N)(small:paceT R.draws.S t b≤1)(A price:ℝ)(amp:Amplitude φ A)
    (sale:∀(z:CellR)(s:Cover),Heard e target (paceT R.draws.S m t) price
      (fun q=>(slice R Q F α ψ X Y z (paceT R.draws.S m b) s t m b older N K N).2 q 0 ω)):
    let ε:=paceT R.draws.S t b
    let take:=panel R Q F α ψ X Y φ y o t m b older N
    Heard e target (paceT R.draws.S m t) ((5*radiusH φ ε y)^4*A*price) (fun q=>take N q 0 ω-take K q 0 ω):=by
  intro ε take
  let T:=paceT R.draws.S m t
  have paid:0≤(T^target)⁻¹*price:=(norm_nonneg _).trans ((sale zeroC 0).1 0 (Nat.zero_le _))
  apply WilsonSeparatedPrefixMovingBeforeRead.heard _ _ _ _ _ (pace_pos ..);intro q hq
  have read (s:Cover)(z:CellR)(i:ℕ)(year:R.anchor ≤ i)(past:older ≤ i)(top:i ≤ N):=
    congrArg (fun Z:Era G ℝ=>Z.2 q 0 ω)
      (WilsonSeparatedPrefixMovingPinProduct.original R Q F roster far α ψ X Y s (paceT R.draws.S m b) t m b older N i z year past top)
  apply (WilsonSeparatedPrefixMovingPinCanvas.original φ ε y o A ((T^target)⁻¹*price) amp paid (pace_pos ..) small _ _ ?_).trans
  · dsimp only [T];ring_nf;exact le_rfl
  intro s _ z
  change ‖(locale z (landed _ _ _ _ _ _ _ s _ t m b older N N)).2 q 0 ω-
    (locale z (landed _ _ _ _ _ _ _ s _ t m b older N K)).2 q 0 ω‖≤_
  rw [read s z N (enrolled.trans cut) (past.trans cut) le_rfl,read s z K enrolled past cut]
  exact (sale z s).1 q hq

end YM.Integration.WilsonSeparatedPrefixMovingPinSuffixPanel
