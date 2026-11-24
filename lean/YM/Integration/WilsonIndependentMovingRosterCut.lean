import YM.Integration.WilsonIndependentMatchedRosterChronology
import YM.Integration.WilsonSeparatedPrefixMovingNativeCut
import YM.Integration.WilsonSeparatedPrefixMovingUnformedSector

/-! The far field is tested against the complete conditional product of
the near roster on a single nominated Mer history. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMovingRosterCut
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e n:ℕ}{E:Credit}
def parcel (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)
    (o:CellR)(y:ℝ)(m i N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) N i (Ashore Q R.draws R.paid φ X m N N y o)

theorem located {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)
    (roster:HorizonP H R W V Q)(φ:Wilt Q)(X:Herit Q)(o:CellR)(y:ℝ)(m i N:ℕ)
    (live:R.anchor ≤ N)(top:i ≤ N):
    parcel R Q φ X o y m i N=locale o (LodeStar R.draws R.paid φ X m i N y):=by
  unfold parcel locale LodeStar
  rw [cruiseT (century o) _ top R.hG R.green le_rfl (Hearth_enter roster φ X live le_rfl),ash_spans]

def contribution (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N:ℕ)(i:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (F.h+capP Q) i older (JoinGap R.draws R.paid i N F.h (capP Q)
    (current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o) (parcel R Q φ X o y m (i+1) N))

def residual (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N:ℕ):Era G ℝ:=
  let exterior i:=current R F ψ Y t i N (y/paceT R.draws.S m t) o
  cruises R.draws R.paid N (F.h+capP Q) N older
    (agateV (exterior N) (Ashore Q R.draws R.paid φ X m N N y o))-
    cruises R.draws R.paid N (F.h+capP Q) m older (agateV (exterior m) (parcel R Q φ X o y m m N))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N:ℕ)(live:R.anchor ≤ t)(base:t ≤ m)
    (ear:older ≤ m)(top:m ≤ N):
    residual R Q F φ ψ X Y o y t m older N=
      ∑d∈range (N-m),contribution R Q F φ ψ X Y o y t m older N (m+d):=by
  let exterior i:=current R F ψ Y t i N (y/paceT R.draws.S m t) o
  let near i:=parcel R Q φ X o y m i N
  have length:m+(N-m)=N:=by omega
  have sworn:Auth (capP Q) (Ashore Q R.draws R.paid φ X m N N y o):=
    ash_head roster φ X (live.trans (base.trans top)) le_rfl o
  have lifted:=WilsonSeparatedPrefixMovingSignedChronology.split R F.h (capP Q) older m N (N-m) ear length.le
    (fun d=>exterior (m+d)) (fun d=>near (m+d))
    (fun d hd=>grades R F far ψ Y o _ t _ N (by omega) (by omega))
    (fun d hd=>cruising R.draws R.hG R.green (by omega:m+d ≤ N) le_rfl sworn)
    (fun d hd=>step R F far ψ Y o _ t _ N live (by omega) (by omega))
    (fun d hd=>(cruises_sub R.draws R.paid N (capP Q) _ (by omega:m+d<N)).symm)
  have paid:=congrArg (fun u:Era G ℝ=>u-cruises R.draws R.paid N (F.h+capP Q) m older
    (agateV (exterior m) (near m))) lifted
  simpa only [length,near,parcel,cruises_top,Nat.add_zero,Nat.add_assoc,exterior,contribution,residual,
    add_sub_cancel_left] using paid

end YM.Integration.WilsonIndependentMovingRosterCut
