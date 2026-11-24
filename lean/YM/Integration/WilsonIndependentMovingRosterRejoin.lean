import YM.Integration.WilsonIndependentMovingRosterCut
import YM.Integration.WilsonSeparatedPrefixMovingFirstTree

/-! Regroup the complete conditional near product at its next meeting with
the far field, preserving all ordinary partners in each earlier near birth. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMovingRosterRejoin
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterCut (parcel contribution)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonSeparatedPrefixMovingUnformedSector (fresh)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

def stored (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(X:Herit Q)(o:CellR)(y:ℝ)(m i j N:ℕ):Era G ℝ:=
  cruises R.draws R.paid N (capP Q) j (i+1) (Ash R.draws R.paid φ X m j N y o)

def crossed (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i j:ℕ):ℝ:=
  if i<j then
    let far:=current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o
    (cruises R.draws R.paid N (F.h+capP Q) i older
      (JoinGap R.draws R.paid i N F.h (capP Q) far (stored R Q φ X o y m i j N))).2 q 0 ω
  else 0

theorem entered {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)
    (roster:HorizonP H R W V Q)(φ:Wilt Q)(X:Herit Q)(o:CellR)(y:ℝ)(m i j N:ℕ)
    (live:R.anchor ≤ m)(start:m ≤ j)(formed:i+1 ≤ j)(edge:j<N):
    Auth (capP Q) (stored R Q φ X o y m i j N):=by
  apply cruising R.draws R.hG R.green formed edge.le
  rw [ash_tide roster φ X live start edge o]
  exact (Auth.verse R.draws edge R.hG R.green (ash_head roster φ X (by omega) (by omega) o)).sub
    (ash_head roster φ X (by omega) edge.le o)

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older i N q:ℕ)(ω:Fin 0→YForest G)
    (live:R.anchor ≤ t)(start:t ≤ m)(route:m ≤ i)(ear:older ≤ i)(edge:i<N):
    (contribution R Q F φ ψ X Y o y t m older N i).2 q 0 ω=
      fresh R Q F φ ψ X Y o y t m older N q ω i+
        ∑j∈range (N-(i+1)),crossed R Q F φ ψ X Y o y t m older N q ω i (i+1+j):=by
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
      P,top,Nat.add_zero,Nat.add_assoc,show i+(1+len)=N by omega,parcel,freshNear,pending,stored,Ashore,Ash] using first
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
  have signed:=WilsonSeparatedPrefixMovingSignedChronology.read R (F.h+capP Q) i older N len ear edge.le
    (join freshNear) (fun j=>join (pending j)) (valid _ freshAuth) (fun j hj=>valid _ (pendingAuth j hj))
  rw [←whole] at signed
  apply Eq.trans (congrArg (fun M:Era G ℝ=>M.2 q 0 ω) signed)
  change (cruises R.draws R.paid N (F.h+capP Q) i older (join freshNear)+
    ∑j∈range len,cruises R.draws R.paid N (F.h+capP Q) i older (join (pending j))).2 q 0 ω=_
  simp only [Prod.snd_add,Pi.add_apply,Prod.snd_sum,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [crossed,if_pos (show i < i+1+j by omega)]

end YM.Integration.WilsonIndependentMovingRosterRejoin
