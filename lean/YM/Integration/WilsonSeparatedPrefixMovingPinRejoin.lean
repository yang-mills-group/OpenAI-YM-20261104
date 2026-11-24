import YM.Integration.WilsonIndependentMovingRosterRejoin
import YM.Integration.WilsonSeparatedPrefixMovingPinDay
import YM.Integration.WilsonSeparatedPrefixMovingPinFlow
import YM.Integration.WilsonSeparatedPrefixMovingUnformedSector

/-! Keep all previously formed near deposits in the same pinned outer return. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinRejoin
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterCut (parcel contribution)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonSeparatedPrefixMovingUnformedSector (fresh)
open WilsonIndependentMovingRosterRejoin (stored entered)
open WilsonSeparatedPrefixMovingPinFlow (born)
open WilsonSeparatedPrefixMovingPinController (appointed)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingUnformedSector (mountedRow)
open WilsonSeparatedPrefixMovingPinDay (crossed)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m b older i N q:ℕ)(site:Cover)(ω:Fin 0→YForest G)
    (live:R.anchor ≤ t)(start:t ≤ m)(route:m ≤ i)(ear:older ≤ i)(edge:i<N):
    (hear R (F.h+capP Q) N b older site i (born R Q F φ ψ X Y o y t m N i)).2 q 0 ω=
      mountedRow R (appointed G e R.draws.S b site) Q F φ ψ X Y o y t m older N q ω i+
        ∑j∈range (N-(i+1)),crossed R (appointed G e R.draws.S b site) Q F φ ψ X Y o y t m older N q ω i (i+1+j):=by
  let len:=N-(i+1)
  have top:i+1+len=N:=by dsimp [len];omega
  let P s j:=WilsonCoeffUV.Mer.awaken Q R.draws R.paid φ X m (i+1+j) N y o s
  let outer:=current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o
  let join (M:Era G ℝ):=JoinGap R.draws R.paid i N F.h (capP Q) outer M
  let pending j:=stored R Q φ X o y m i (i+1+j) N
  let freshNear:=Ashore Q R.draws R.paid φ X m (i+1) N y o
  have first:=WilsonIndependentMatchedRosterChronology.original R (i+1) N len top.le (asp Q) P
    (fun s j hj=>grades R (Q s) (roster s).some (φ s) (X s) o y m _ N (by omega) (by omega))
    (fun s j hj=>step R (Q s) (roster s).some (φ s) (X s) o y m _ N (live.trans start) (by omega) (by omega))
  have parsed:parcel R Q φ X o y m (i+1) N=freshNear+∑j∈range len,pending j:=by
    simpa only [WilsonIndependentMatchedRosterChronology.mass,WilsonIndependentMatchedRosterChronology.born,
      P,top,Nat.add_zero,Nat.add_assoc,show i+(1+len)=N by omega,parcel,freshNear,pending,WilsonIndependentMovingRosterRejoin.stored,Ashore,Ash] using first
  have outAuth:Auth F.h outer:=grades R F far ψ Y o _ t _ N (by omega) edge
  have freshAuth:Auth (capP Q) freshNear:=ash_head roster φ X (by omega) edge o
  have pendingAuth:∀j<len,Auth (capP Q) (pending j):=fun j hj=>
    entered R Q roster φ X o y m i _ N (live.trans start) (by omega) (by omega) (by omega)
  have valid (M:Era G ℝ)(hm:Auth (capP Q) M):Auth (F.h+capP Q) (join M):=
    (Auth.verse R.draws edge R.hG R.green (outAuth.manor hm)).sub
      ((Auth.verse R.draws edge R.hG R.green outAuth).manor (Auth.verse R.draws edge R.hG R.green hm))
  have whole:join (parcel R Q φ X o y m (i+1) N)=join freshNear+∑j∈range len,join (pending j):=by
    rw [parsed]
    apply WilsonSeparatedPrefixMovingFirstTree.parse R.draws R.paid N i F.h (capP Q) len R.hG R.green edge
      outer _ pending outAuth freshAuth pendingAuth
  have signed:=WilsonSeparatedPrefixMovingPinHearing.register R (F.h+capP Q) N b older i len site
    (join freshNear) (fun j=>join (pending j)) ear edge.le (valid _ freshAuth) (fun j hj=>valid _ (pendingAuth j hj))
  rw [←whole] at signed
  apply Eq.trans (congrArg (fun M:Era G ℝ=>M.2 q 0 ω) signed)
  simp only [Prod.snd_add,Pi.add_apply,Prod.snd_sum,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [WilsonSeparatedPrefixMovingPinDay.crossed,if_pos (show i < i+1+j by omega)]
  rfl

end YM.Integration.WilsonSeparatedPrefixMovingPinRejoin
