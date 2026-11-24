import YM.Integration.WilsonMovingForkSharpFineBirth
import YM.Integration.WilsonSeparatedPrefixMovingNativeCut

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramBirth
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

open WilsonSeparatedPrefixMovingUnformedSector (fresh invoice)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
def pair (R:Realm G (e+1) E)(A B:SealR G)(φ:Rarity A.D)(ψ:Rarity B.D)(X:A.Rider)(Z:B.Rider)
    (o:CellR)(y:ℝ)(t i older N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (A.h+B.h) i older
    (agateV (current R A φ X t i N y o) (current R B ψ Z t i N y o))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(A B:SealR G)
    (left:PassportC H R A W V)(right:PassportC H R B W V)(φ:Rarity A.D)(ψ:Rarity B.D)
    (X:A.Rider)(Z:B.Rider)(o:CellR)(y:ℝ)(t b older N q:ℕ)(w:Fin 0→YForest G)
    (gate:R.anchor ≤ t)(start:t ≤ b)(age:older ≤ b)(cut:b ≤ N):
    (pair R A B φ ψ X Z o y t N older N).2 q 0 w-(pair R A B φ ψ X Z o y t b older N).2 q 0 w =
      ∑i∈range (N-b),fresh R (fun _:Fin 1=>B) A (fun _=>ψ) φ (fun _=>Z) X o y t t older N q w (b+i):=by
  let P:=fun i=>current R A φ X t (b+i) N y o
  let Q:=fun i=>current R B ψ Z t (b+i) N y o
  have len:b+(N-b)=N:=by omega
  have issue:=WilsonSeparatedPrefixMovingSignedChronology.split R A.h B.h older b N (N-b) age len.le P Q
    (fun i hi=>grades R A left φ X o y t _ N (by omega) (by omega))
    (fun i hi=>grades R B right ψ Z o y t _ N (by omega) (by omega))
    (fun i hi=>step R A left φ X o y t _ N gate (by omega) (by omega))
    (fun i hi=>step R B right ψ Z o y t _ N gate (by omega) (by omega))
  have read:=congrArg (fun T:Era G ℝ=>T.2 q 0 w) issue
  have desc (U:Finset ℕ)(rows:ℕ→Era G ℝ):
      (∑j∈U,rows j).2 q 0 w=∑j∈U,(rows j).2 q 0 w:=by
    induction U using Finset.induction_on with
    | empty=>simp
    | insert i set hi ih=>simp [hi,ih]
  have unit:paceT R.draws.S t t=1:=div_self (R.draws.S.a_pos _).ne'
  simp only [P,Q,len,Nat.add_zero,Prod.snd_add,Pi.add_apply,desc] at read
  unfold pair
  rw [read,add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i _
  simp [fresh,MassP,unit,Nat.add_assoc]
end YM.Integration.WilsonMovingForkSharpGramBirth
