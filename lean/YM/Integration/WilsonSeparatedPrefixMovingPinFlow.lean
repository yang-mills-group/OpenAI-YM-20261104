import YM.Integration.WilsonIndependentMovingRosterCut
import YM.Integration.WilsonSeparatedPrefixMovingPinHearing

/-! Exact first-contact chronology under a lattice pin from the appointed common older date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinFlow
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e n:ℕ}{E:Credit}
def packet (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m N i:ℕ):Era G ℝ:=
  agateV (current R F ψ Y t i N (y/paceT R.draws.S m t) o) (parcel R Q φ X o y m i N)

def born (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m N i:ℕ):Era G ℝ:=
  JoinGap R.draws R.paid i N F.h (capP Q) (current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o)
    (parcel R Q φ X o y m (i+1) N)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older l N length:ℕ)
    (horizon:R.anchor ≤ t)(anchored:t ≤ l)(before:older ≤ b)(late:b ≤ l)(duration:l+length ≤ N):
    let ask:=hear R (F.h+capP Q) N b older a
    let P:=packet R Q F φ ψ X Y o y t m N
    let D:=born R Q F φ ψ X Y o y t m N
    ask (l+length) (P (l+length))-ask l (P l)=
      ∑d∈range length,ask (l+d) (D (l+d)):=by
  intro ask P D
  let outer i:=current R F ψ Y t i N (y/paceT R.draws.S m t) o
  let near i:=parcel R Q φ X o y m i N
  have valid:Auth (capP Q) (Ashore Q R.draws R.paid φ X m N N y o):=
    ash_head roster φ X (by omega) le_rfl o
  have pay:=WilsonSeparatedPrefixMovingPinHearing.split R F.h (capP Q) b older l N length a before late
    duration (fun d=>outer (l+d)) (fun d=>near (l+d))
    (fun d hd=>grades R F far ψ Y o _ t _ N (by omega) (by omega))
    (fun d hd=>cruising R.draws R.hG R.green (by omega:l+d ≤ N) le_rfl valid)
    (fun d hd=>step R F far ψ Y o _ t _ N horizon (by omega) (by omega))
    (fun d hd=>(cruises_sub R.draws R.paid N (capP Q) _ (by omega:l+d<N)).symm)
  have sum:=congrArg (fun U:Era G ℝ=>U-ask l (P l)) pay
  simpa only [ask,P,D,packet,born,near,outer,Nat.add_zero,Nat.add_assoc,add_sub_cancel_left] using sum

theorem endpoints {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)
    (t m b N:ℕ)(live:R.anchor ≤ N)(time:b ≤ N):
    packet R Q F φ ψ X Y o y t m N N=
      agateV (current R F ψ Y t N N (y/paceT R.draws.S m t) o) (Ashore Q R.draws R.paid φ X m N N y o) ∧
    packet R Q F φ ψ X Y o y t m N b=
      agateV (current R F ψ Y t b N (y/paceT R.draws.S m t) o) (locale o (LodeStar R.draws R.paid φ X m b N y)):=by
  constructor
  · unfold packet parcel;rw [cruises_top]
  · unfold packet;rw [WilsonIndependentMovingRosterCut.located R Q roster φ X o y m b N live time]

end YM.Integration.WilsonSeparatedPrefixMovingPinFlow
