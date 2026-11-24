import YM.Integration.WilsonIndependentMovingRosterCut
import YM.Integration.WilsonSeparatedPrefixMovingMiddleSector

/-! Use the same true located near roster at both cuts. Its coefficients
at b contain all earlier local joins, conditional means, and the unit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMiddleLaw

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel located contribution)
open Finset
open scoped Classical BigOperators Topology

variable {G:Gauge}{e n:ℕ}{E:Credit}
def composite (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N b:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (F.h+capP Q) b older (agateV
    (current R F ψ Y t b N (y/paceT R.draws.S m t) o) (locale o (LodeStar R.draws R.paid φ X m b N y)))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t b m older N:ℕ)(live:R.anchor ≤ t)(home:t ≤ b)
    (ear:older ≤ b)(fine:b ≤ m)(top:m ≤ N)(q:ℕ)(ω:Fin 0→YForest G):
    (composite R Q F φ ψ X Y o y t m older N m).2 q 0 ω-
      (composite R Q F φ ψ X Y o y t m older N b).2 q 0 ω=
      ∑d∈range (m-b),WilsonSeparatedPrefixMovingMiddleSector.joined R Q F φ ψ X Y o y t m older N q ω (b+d):=by
  let outside i:=current R F ψ Y t i N (y/paceT R.draws.S m t) o
  let near i:=parcel R Q φ X o y m i N
  have endAt:b+(m-b)=m:=by omega
  have atTop:R.anchor ≤ N:=by omega
  have origin:Auth (capP Q) (Ashore Q R.draws R.paid φ X m N N y o):=ash_head roster φ X atTop le_rfl o
  have law:=WilsonSeparatedPrefixMovingSignedChronology.split R F.h (capP Q) older b N (m-b) ear
    (by omega) (fun d=>outside (b+d)) (fun d=>near (b+d))
    (fun d hd=>grades R F far ψ Y o _ t _ N (by omega) (by omega))
    (fun d hd=>cruising R.draws R.hG R.green (by omega:b+d ≤ N) le_rfl origin)
    (fun d hd=>step R F far ψ Y o _ t _ N live (by omega) (by omega))
    (fun d hd=>(cruises_sub R.draws R.paid N (capP Q) _ (by omega:b+d<N)).symm)
  have placed:=congrArg (fun x:Era G ℝ =>x.2 q 0 ω) law
  simp only [near,outside,Prod.snd_add,Prod.snd_sum,Pi.add_apply,Finset.sum_apply,endAt,Nat.add_zero] at placed
  have all:∀i ≤ N,parcel R Q φ X o y m i N=locale o (LodeStar R.draws R.paid φ X m i N y):=
    fun i hi=>located R Q roster φ X o y m i N atTop hi
  rw [all m top,all b (fine.trans top)] at placed
  have actual:(composite R Q F φ ψ X Y o y t m older N m).2 q 0 ω=
      (composite R Q F φ ψ X Y o y t m older N b).2 q 0 ω+
      ∑d∈range (m-b),(contribution R Q F φ ψ X Y o y t m older N (b+d)).2 q 0 ω:=placed
  rw [actual,add_sub_cancel_left]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have date:=mem_range.mp hd
  have next:b+d+1 ≤ N:=by omega
  unfold WilsonSeparatedPrefixMovingMiddleSector.joined contribution
  rw [all (b+d+1) next]

end YM.Integration.WilsonSeparatedPrefixMovingMiddleLaw
