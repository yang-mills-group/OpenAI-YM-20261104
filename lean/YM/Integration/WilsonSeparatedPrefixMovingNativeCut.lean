import YM.Integration.WilsonSeparatedPrefixMovingSignedChronology
import YM.Integration.WilsonSeparatedPrefixMovingPairSector

/-! The exact mixed face at a fixed older receiver. Old deposits remain in
the conditional product through every subsequent edge. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingNativeCut
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e:ℕ}{E:Credit}

theorem grades {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:SealR G)(ticket:PassportC H R Q W V)
    (φ:Rarity Q.D)(X:Q.Rider)(o:CellR)(y:ℝ)(t i N:ℕ)(live:R.anchor ≤ i)(top:i ≤ N):
    Auth Q.h (current R Q φ X t i N y o):=locale_val _ (passportHead (m:=t) ticket φ X y live top) o

theorem step {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:SealR G)(ticket:PassportC H R Q W V)
    (φ:Rarity Q.D)(X:Q.Rider)(o:CellR)(y:ℝ)(t i N:ℕ)(live:R.anchor ≤ t)(after:t ≤ i)(edge:i<N):
    verseI R.draws R.paid i N Q.h (current R Q φ X t (i+1) N y o)=current R Q φ X t i N y o:=
  passportCarry ticket φ X o live after edge

def joined (R:Realm G (e+1) E)(A B:SealR G)(φ:Rarity A.D)(ψ:Rarity B.D)(X:A.Rider)(Y:B.Rider)
    (o:CellR)(y:ℝ)(m i N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (A.h+B.h) N i (agateV (current R A φ X m N N y o) (current R B ψ Y m N N y o))

def before (R:Realm G (e+1) E)(A B F:SealR G)(φ:Rarity A.D)(ψ:Rarity B.D)(χ:Rarity F.D)
    (X:A.Rider)(Y:B.Rider)(Z:F.Rider)(o:CellR)(y:ℝ)(t m older N i:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (F.h+(A.h+B.h)) i older (JoinGap R.draws R.paid i N F.h (A.h+B.h)
    (current R F χ Z t (i+1) N (y/paceT R.draws.S m t) o) (joined R A B φ ψ X Y o y m (i+1) N))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(A B F:SealR G)
    (left:PassportC H R A W V)(right:PassportC H R B W V)(outer:PassportC H R F W V)
    (φ:Rarity A.D)(ψ:Rarity B.D)(χ:Rarity F.D)(X:A.Rider)(Y:B.Rider)(Z:F.Rider)
    (o:CellR)(y:ℝ)(t m older N:ℕ)(live:R.anchor ≤ t)(start:t ≤ m)(late:older ≤ m)(top:m ≤ N):
    let ext:=fun i=>current R F χ Z t i N (y/paceT R.draws.S m t) o
    let near:=fun i=>joined R A B φ ψ X Y o y m i N
    cruises R.draws R.paid N (F.h+(A.h+B.h)) N older (agateV (ext N)
      (agateV (current R A φ X m N N y o) (current R B ψ Y m N N y o))) =
      cruises R.draws R.paid N (F.h+(A.h+B.h)) m older (agateV (ext m) (near m))+
        ∑d∈range (N-m),before R A B F φ ψ χ X Y Z o y t m older N (m+d):=by
  intro ext near
  have len:m+(N-m)=N:=by omega
  have awake:=live.trans (start.trans top)
  have raw:= (grades R A left φ X o y m N N awake le_rfl).manor (grades R B right ψ Y o y m N N awake le_rfl)
  have pass:=WilsonSeparatedPrefixMovingSignedChronology.split R F.h (A.h+B.h) older m N (N-m) late
    (le_of_eq len) (fun j=>ext (m+j)) (fun j=>near (m+j))
    (fun j hj=>grades R F outer χ Z o _ t _ N (by omega) (by omega))
    (fun j hj=>cruising R.draws R.hG R.green (by omega: m+j ≤ N) le_rfl raw)
    (fun j hj=>step R F outer χ Z o _ t _ N live (by omega) (by omega))
    (fun j hj=>(cruises_sub R.draws R.paid N (A.h+B.h) _ (by omega:m+j<N)).symm)
  simpa only [len,near,joined,cruises_top,Nat.add_zero,Nat.add_assoc,before] using pass

end YM.Integration.WilsonSeparatedPrefixMovingNativeCut
