import YM.Integration.WilsonSeparatedPrefixMovingTriangle
import YM.Integration.WilsonSeparatedPrefixMovingPinRejoin
import YM.Integration.WilsonSeparatedPrefixMovingMiddleSector

/-! Split the pinned upper return by its actual first near-to-far connection. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinSigned
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
def slice (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older N lo hi:ℕ):Era G ℝ:=
  let ask:=hear R (F.h+capP Q) N b older a
  let P:=packet R Q F φ ψ X Y o y t m N
  ask hi (P hi)-ask lo (P lo)

theorem fine {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older N q:ℕ)(ω:Fin 0→YForest G)
    (horizon:R.anchor ≤ t)(anchored:t ≤ m)(before:older ≤ b)(dated:b ≤ m)(stop:m ≤ N):
    let sites:=appointed G e R.draws.S b a
    (slice R Q F φ ψ X Y o y a t m b older N m N).2 q 0 ω=
      (∑d∈range (N-m),WilsonSeparatedPrefixMovingUnformedSector.mountedRow R sites Q F φ ψ X Y o y t m older N q ω (m+d))+
      ∑d∈range (N-m),∑j∈(range (N-m)).filter (fun j=>d ≤ j),
        WilsonSeparatedPrefixMovingPinDay.crossed R sites Q F φ ψ X Y o y t m older N q ω (m+d) (m+j):=by
  intro sites
  have length:m+(N-m)=N:=by omega
  have receipt:=WilsonSeparatedPrefixMovingPinFlow.original R Q F roster far φ ψ X Y o y a t m b older m N (N-m)
    horizon anchored before dated length.le
  dsimp only at receipt
  rw [length] at receipt
  rw [slice,receipt]
  simp only [Prod.snd_sum,Finset.sum_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have fine:=mem_range.mp hd
  rw [WilsonSeparatedPrefixMovingPinRejoin.original R Q F roster far φ ψ X Y o y t m b older (m+d) N q a ω
    horizon anchored (by omega) (by omega) (by omega)]
  congr 1
  have move:=WilsonSeparatedPrefixMovingTriangle.row N m d fine
    (fun j=>WilsonSeparatedPrefixMovingPinDay.crossed R sites Q F φ ψ X Y o y t m older N q ω (m+d) (m+j))
    (by simp [WilsonSeparatedPrefixMovingPinDay.crossed])
  simpa only [Nat.add_assoc,Nat.add_comm 1 d,Nat.add_left_comm] using move

theorem middle {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older N q:ℕ)(ω:Fin 0→YForest G)
    (horizon:R.anchor ≤ t)(anchored:t ≤ b)(before:older ≤ b)(dated:b ≤ m)(stop:m ≤ N):
    (slice R Q F φ ψ X Y o y a t m b older N b m).2 q 0 ω=∑d∈range (m-b),
      WilsonSeparatedPrefixMovingMiddleSector.mountedRow R (appointed G e R.draws.S b a)
        Q F φ ψ X Y o y t m older N q ω (b+d):=by
  have length:b+(m-b)=m:=by omega
  have receipt:=WilsonSeparatedPrefixMovingPinFlow.original R Q F roster far φ ψ X Y o y a t m b older b N (m-b)
    horizon anchored before le_rfl (by omega)
  dsimp only at receipt
  rw [length] at receipt
  rw [slice,receipt]
  simp only [Prod.snd_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have fine:=mem_range.mp hd
  unfold WilsonSeparatedPrefixMovingPinFlow.born
  rw [WilsonIndependentMovingRosterCut.located R Q roster φ X o y m (b+d+1) N (by omega) (by omega)]
  rfl

theorem regroup (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(a:Cover)(t m b older N:ℕ):
    slice R Q F φ ψ X Y o y a t m b older N b N=
      slice R Q F φ ψ X Y o y a t m b older N m N+slice R Q F φ ψ X Y o y a t m b older N b m:=by
  dsimp only [slice];exact (sub_add_sub_cancel _ _ _).symm

end YM.Integration.WilsonSeparatedPrefixMovingPinSigned
