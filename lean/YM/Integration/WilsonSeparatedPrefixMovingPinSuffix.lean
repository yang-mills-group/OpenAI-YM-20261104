import YM.Integration.WilsonSeparatedPrefixMovingTriangle
import YM.Integration.WilsonSeparatedPrefixMovingPinSigned
import YM.Integration.WilsonSeparatedPrefixMovingDatedSites
import YM.Integration.WilsonSeparatedPrefixMovingPinRejoin
import YM.Integration.WilsonSeparatedPrefixMovingMiddleSector

/-! Split the pinned upper return by its actual first near-to-far connection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinSuffix
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingPinFlow (packet born)
open WilsonSeparatedPrefixMovingPinController (appointed)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e n:ℕ}{E:Credit}

open WilsonSeparatedPrefixMovingPinSigned (slice)
open WilsonSeparatedPrefixMovingUnformedSector (mountedRow)
open WilsonSeparatedPrefixMovingPinDay (crossed)
open WilsonSeparatedPrefixMovingDatedSites (select)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older N K q:ℕ)(ω:Fin 0→YForest G)
    (horizon:R.anchor ≤ t)(anchored:t ≤ m)(before:older ≤ b)(dated:b ≤ m)(cut:m ≤ K)(stop:K ≤ N):
    let sites:=select (appointed G e R.draws.S b a) K
    (slice R Q F φ ψ X Y o y a t m b older N K N).2 q 0 ω=
      (∑d∈range (N-m),mountedRow R sites Q F φ ψ X Y o y t m older N q ω (m+d))+
      ∑d∈range (N-m),∑j∈(range (N-m)).filter (fun j=>d ≤ j),
        crossed R sites Q F φ ψ X Y o y t m older N q ω (m+d) (m+j):=by
  intro sites
  let pin:=appointed G e R.draws.S b a
  let pay i:=(hear R (F.h+capP Q) N b older a i (born R Q F φ ψ X Y o y t m N i)).2 q 0 ω
  have length:K+(N-K)=N:=by omega
  have receipt:=WilsonSeparatedPrefixMovingPinFlow.original R Q F roster far φ ψ X Y o y a t m b older K N (N-K)
    horizon (anchored.trans cut) before (dated.trans cut) length.le
  dsimp only at receipt
  rw [length] at receipt
  rw [WilsonSeparatedPrefixMovingPinSigned.slice,receipt]
  simp only [Prod.snd_sum,Finset.sum_apply]
  change ∑d∈range (N-K),pay (K+d)=_
  rw [←WilsonSeparatedPrefixMovingDatedSites.original pay m K N cut stop,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have small:=Finset.mem_range.mp hd
  have lo:older ≤ m+d:=by omega
  have hi:m+d ≤ N:=by omega
  rw [WilsonSeparatedPrefixMovingDatedSites.fresh R pin K Q F φ ψ X Y o y t m older N q ω (m+d) lo hi]
  have row (j:ℕ):crossed R sites Q F φ ψ X Y o y t m older N q ω (m+d) (m+j)=
      if K ≤ m+d then crossed R pin Q F φ ψ X Y o y t m older N q ω (m+d) (m+j) else 0:=
    WilsonSeparatedPrefixMovingDatedSites.crossed R pin K Q F φ ψ X Y o y t m older N q ω (m+d) (m+j) lo hi
  simp_rw [row]
  by_cases selected:K ≤ m+d
  · simp only [if_pos selected]
    dsimp only [pay]
    rw [WilsonSeparatedPrefixMovingPinRejoin.original R Q F roster far φ ψ X Y o y t m b older (m+d) N q a ω
      horizon anchored (by omega) lo (by omega)]
    congr 1
    have move:=WilsonSeparatedPrefixMovingTriangle.row N m d small
      (fun j=>crossed R pin Q F φ ψ X Y o y t m older N q ω (m+d) (m+j))
      (by simp [WilsonSeparatedPrefixMovingPinDay.crossed])
    simpa only [Nat.add_assoc,Nat.add_comm 1 d,Nat.add_left_comm] using move
  · simp only [if_neg selected,Finset.sum_const_zero,add_zero]

end YM.Integration.WilsonSeparatedPrefixMovingPinSuffix
