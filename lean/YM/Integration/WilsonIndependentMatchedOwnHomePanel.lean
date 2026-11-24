import YM.Integration.WilsonSeparatedPrefixMovingPinnedRaw

/-! The individual far pivot meets a near product genuinely planted at the
interior date. Keep the earlier deposited near word on the same quiet. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOwnHomePanel
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Mer.Patrol
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonSeparatedPrefixMovingPinCanvas (total)
open WilsonPositionProgramPinnedHearthHistory (pin)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n D e:ℕ}{E W V:Credit}
variable (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(α:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)

def source (t m K N:ℕ)(y:ℝ):Era G Lounge:=
  agateV (F.spins R.draws R.paid ψ t K N (y/paceT R.draws.S m t) Y)
    (HearthC Q R.draws R.paid α X m K N y)
def landed (t m b older K N:ℕ)(y:ℝ)(s:Cover):Era G Lounge:=
  cruises R.draws R.paid N (F.h+capP Q) K older (shifted (source R Q F α ψ X Y t m K N y) (pin R.draws.S b K s))
def born (φ:Rarity D)(y:ℝ)(o:CellR)(t m b older K N j r:ℕ)(w:Fin r→YForest G):ℝ:=
  total φ (paceT R.draws.S t b) y o fun s=>(landed R Q F α ψ X Y t m b older K N (paceT R.draws.S m b) s).2 j r w

theorem placed (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(t m b older K N:ℕ)(y:ℝ)(s:Cover)(z:CellR)
    (gate:R.anchor ≤ K)(old:older ≤ K)(top:K ≤ N):
    locale z (landed R Q F α ψ X Y t m b older K N y s)=hear R (F.h+capP Q) N b older s K
      (agateV (current R F ψ Y t K N (y/paceT R.draws.S m t) z) (Ashore Q R.draws R.paid α X m K N y z)):=by
  have fp:=passportHead far ψ Y (y/paceT R.draws.S m t) gate top (m:=t)
  have np:=Hearth_enter roster α X gate top (m:=m) (y:=y)
  unfold landed source hear locale
  rw [cruiseT (century z) R.draws old R.hG R.green top ((agateHome fp np).shifted (pin R.draws.S b K s))]
  apply congr_arg (cruises R.draws R.paid N (F.h+capP Q) K older)
  change shifted (locale z (agateV _ _)) _=shifted (agateV _ _) _
  rw [woadChart,ash_spans]
  rfl

theorem earlier (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(t m b older K N:ℕ)(y:ℝ)(s:Cover)(z:CellR)
    (gate:R.anchor ≤ K)(old:older ≤ K)(top:K ≤ N):
    locale z (WilsonSeparatedPrefixMovingPinProduct.landed R Q F α ψ X Y s y t m b older N K)-
    locale z (landed R Q F α ψ X Y t m b older K N y s)=
    hear R (F.h+capP Q) N b older s K (agateV (current R F ψ Y t K N (y/paceT R.draws.S m t) z)
      (locale z (LodeStar R.draws R.paid α X m K N y)-Ashore Q R.draws R.paid α X m K N y z)):=by
  rw [WilsonSeparatedPrefixMovingPinProduct.original R Q F roster far α ψ X Y s y t m b older N K z gate old top,
    (WilsonSeparatedPrefixMovingPinFlow.endpoints R Q F roster α ψ X Y z y t m K N (gate.trans top) top).2,
    placed R Q F α ψ X Y roster far t m b older K N y s z gate old top,pairingP]
  have p:=WilsonSeparatedPrefixMovingSummedCenter.mounted R Q F α ψ X Y roster far t m K older N y gate old top
  have f:Auth F.h (current R F ψ Y t K N (y/paceT R.draws.S m t) z):=locale_val _ p.1 z
  exact (WilsonSeparatedPrefixMovingPinHearing.subtract R (F.h+capP Q) N b older K s _ _ old top
    (f.manor (locale_val _ p.2.1 z)) (f.manor (ash_head roster α X gate top z))).symm

theorem original (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Rarity D)(y:ℝ)(o:CellR)
    (t m b older K N j r:ℕ)(w:Fin r→YForest G)(gate:R.anchor ≤ K)(old:older ≤ K)(top:K ≤ N)
    (farScale:t ≤ b)(amp bound:ℝ)(weight:Amplitude φ amp)(positive:0 ≤ bound)
    (held:∀s∈canvasM φ (paceT R.draws.S t b) y,∀z:CellR,
      ‖(hear R (F.h+capP Q) N b older s K (agateV (current R F ψ Y t K N (paceT R.draws.S m b/paceT R.draws.S m t) z)
        (locale z (LodeStar R.draws R.paid α X m K N (paceT R.draws.S m b))-
          Ashore Q R.draws R.paid α X m K N (paceT R.draws.S m b) z))).2 j r w‖ ≤ bound):
    ‖panel R Q F α ψ X Y φ y o t m b older N K j r w-born R Q F α ψ X Y φ y o t m b older K N j r w‖ ≤
    (5*radiusH φ (paceT R.draws.S t b) y)^4*amp*bound:=by
  apply WilsonSeparatedPrefixMovingPinCanvas.original _ _ _ _ _ _ weight positive (pace_pos ..) (pace_le _ farScale)
  intro s hs z
  change ‖(locale z (WilsonSeparatedPrefixMovingPinProduct.landed R Q F α ψ X Y s (paceT R.draws.S m b) t m b older N K)).2 j r w-
    (locale z (landed R Q F α ψ X Y t m b older K N (paceT R.draws.S m b) s)).2 j r w‖ ≤ bound
  have app:=congrArg (fun P:Era G ℝ=>P.2 j r w)
    (earlier R Q F α ψ X Y roster far t m b older K N (paceT R.draws.S m b) s z gate old top)
  exact (congrArg norm app).le.trans (held s hs z)

end YM.Integration.WilsonIndependentMatchedOwnHomePanel
end
