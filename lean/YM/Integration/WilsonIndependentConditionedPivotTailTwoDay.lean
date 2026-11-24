import YM.Integration.WilsonIndependentConditionedPivotTailWing
import YM.Integration.WilsonIndependentConditionedPivotTailHomes
import YM.Integration.WilsonIndependentConditionedPivotTailLocalSale

/-! A true first union of separately normalized near and outer slots on the
inherited vacuum, with the coarse price of the literal union and all peers. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailTwoDay
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (printed)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterStableMoney (fees)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentConditionedPivotTailHomes (rows first)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{n e:ℕ}{E W V:Credit}
local notation "I" => Fin ((n+1)+1)

def allowance (H:Hol G)(Q:I→SealR G)(X:Herit Q)(e b:ℕ)(E W V:Credit)(Z:ℝ):I→ℝ:=
  fun s=>(WilsonIndependentConditionedPivotTailWing.price H (Q s) e b E W V).buy Z*fee (Q s) e (X s)

theorem original (R:Realm G (e+1) E)(Q:I→SealR G)(roster:HorizonP H R W V Q)(b:ℕ)(sale:SpringD R (capP Q) 0 b W)
    (host t m j N:ℕ)(live:R.anchor ≤ host)(fromHost:host ≤ t)(away:t ≤ m)(front:m ≤ j)(atEdge:j<N)
    (φ:Wilt Q)(X:Herit Q)(B:I→ℝ)(y z gap:ℝ)(o:CellR):
    let T:=paceT R.draws.S m t
    let x:=paceT R.draws.S m (j+1)
    let r:=paceT R.draws.S m j
    let δ:=paceT R.draws.S m N
    let A:=allowance H Q X e b E W V (epoch R host (j+1))
    let Z:=first R Q φ X (homes t m) (centers y T) (fun _=>o) j N
    0 < gap → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 (centers y T s) ≤ z) →
    (∀s s':Fin (n+1),s≠s'→ClearDay (φ s.succ) (φ s'.succ) gap) →
    (∀s:Fin (n+1),∀p∈tsupport (φ s.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p (T • q)) →
      Auth (capP Q) Z ∧ Flush e 0 r Z
        (T^(Q 0).h*((n+1:ℕ)*R.cash (priceWG G e (capP Q) 0 b E W) j*pearlB 0 b (4*z) (gap/r)*
          nuP (coinMat (capP Q) e+1) (n+1) (fun s=>offer 0 b (Q s).h 0 z δ x (A s) (B s)))):=by
  intro T x r δ A Z positive tested cups clear between
  let d:=fun s=>(Q s).h
  let w:=fun _:I=>(0:ℕ)
  let P:=fun s=>printed R (Q s) (φ s) (X s) (homes t m s) N (centers y T s) o
  have zoom:1 ≤ T:=pace_ge _ away
  have pZ:1 ≤ epoch R host (j+1):=(WilsonSeparatedPrefixMovingCalendar.window R host m (j+1)
    live (fromHost.trans away) (front.trans (Nat.le_succ j))).1
  have AP (s):0 ≤ A s:=mul_nonneg
    (zero_le_one.trans ((WilsonIndependentConditionedPivotTailWing.price H (Q s) e b E W V).purchase pZ))
    (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _)
  have prior (s:I):host ≤ homes t m s:=Fin.cases fromHost (fun _=>fromHost.trans away) s
  have dated (s:I):homes t m s ≤ j:=Fin.cases (away.trans front) (fun _=>front) s
  have authentic (s:I):OnEdge R (d s) 0 b (homes t m s) N j (φ s) (centers y T s) o (P s)
      (fees 0 b d w A B z δ x T s):=by
    have offerAt:=WilsonIndependentConditionedPivotTailWing.original (Q s) R (roster s).some host
      (homes t m s) j N b live (prior s) (dated s) atEdge (φ s) (X s) (B s) (centers y T s) z o (tested s) (cups s)
    convert offerAt using 1
    induction s using Fin.cases with
    | zero=>
      change offer _ _ _ _ _ (δ/T) (x/T) _ _=_
      have a:=WilsonSeparatedPrefixMovingUnformed.rulers R.draws.S t m N
      have c:=WilsonSeparatedPrefixMovingUnformed.rulers R.draws.S t m (j+1)
      simp only [homes,Fin.cons_zero,a,c];rfl
    | succ s=>rfl
  have joined:=WilsonIndependentConditionedPivotTailLocalSale.original R sale t m away front atEdge
    (live.trans (fromHost.trans (away.trans front))) d d w le_rfl φ A B y z gap o P zoom positive AP tested cups clear between authentic
  have actual:(fun s=>P s (j+1-homes t m s))=rows R Q φ X (homes t m) (centers y T) (fun _=>o) (j+1) N:=by
    funext s
    dsimp only [P,printed,rows]
    rw [Nat.add_sub_of_le ((dated s).trans (Nat.le_succ _))]
  simpa only [actual,Z,WilsonIndependentConditionedPivotTailHomes.first,T,δ,x,r,Nat.add_zero,d,w,capP,asp] using joined

end YM.Integration.WilsonIndependentConditionedPivotTailTwoDay

