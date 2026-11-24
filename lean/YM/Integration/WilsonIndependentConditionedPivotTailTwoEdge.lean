import YM.Integration.WilsonIndependentConditionedPivotTailTwoDay
import YM.Integration.WilsonIndependentConditionedPivotTailTwoFees
import YM.Integration.WilsonIndependentMovingRosterStableRetention

/-! A complete first union on the genuine earlier read. Its local moment is
the sum of the filed grades plus the gain; the upper cutoff only labels the
inherited vacuum and the actual dated operands. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailTwoEdge
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentConditionedPivotTailHomes (deposit)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{n e:ℕ}{E W V:Credit}
local notation "I" => Fin ((n+1)+1)

def amount (Q:I→SealR G)(X:Herit Q)(B:I→ℝ)(e b:ℕ)(T gap z:ℝ):ℝ:=
  T^(Q 0).h*profiles (n+1) (capP Q) e 0 b gap z (∏s,factor 0 b z*(B s*fee (Q s) e (X s)))

theorem original (H:Hol G)(Q:I→SealR G)(e gain:ℕ)(E W V:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_roster:HorizonP H R W V Q)
    (_spring:SpringD R (capP Q) 0 (capP Q+gain) W)(_older:Dormitory R (capP Q) 0 V)
    (t m j N:ℕ),R.anchor ≤ t → t ≤ m → m ≤ j → j<N →
    ∀(φ:Wilt Q)(X:Herit Q)(B:I→ℝ)(y z gap:ℝ)(o:CellR),
    let T:=paceT R.draws.S m t
    let Z:=deposit R Q φ X (homes t m) (centers y T) (fun _=>o) m j N
    0 < gap → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 (centers y T s) ≤ z) →
    (∀s s':Fin (n+1),s≠s'→ClearDay (φ s.succ) (φ s'.succ) gap) →
    (∀s:Fin (n+1),∀p∈tsupport (φ s.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p (T • q)) →
      Auth (capP Q) Z ∧ Flush e 0 1 Z
        (C.buy (epoch R t (j+1))*(paceT R.draws.S m (j+1))^gain*amount Q X B e (capP Q+gain) T gap z):=by
  let k:=capP Q
  let b:=k+gain
  let S:=priceWG G e k 0 b E W
  let C:=fun s=>WilsonIndependentConditionedPivotTailWing.price H (Q s) e b E W V
  obtain ⟨D,sold⟩:=WilsonIndependentMovingRosterStableRetention.original (n:=n) G k k e 0 b E W V
  refine ⟨WilsonIndependentConditionedPivotTailTwoFees.total D S E b C,?_⟩
  intro R roster spring older t m j N start away front atEdge φ X B y z gap o T Z pos amp caps clear separated
  let l:=fun s=>(Q s).h
  let w:=fun _:I=>(0:ℕ)
  let era:=WilsonIndependentConditionedPivotTailHomes.first R Q φ X (homes t m) (centers y T) (fun _=>o) j N
  let now:=epoch R t (j+1)
  let A:=WilsonIndependentConditionedPivotTailTwoDay.allowance H Q X e b E W V now
  let L:ℝ:=(ll R.draws j).L.val
  let bill:=D.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*L^k
  have issued:=WilsonIndependentConditionedPivotTailTwoDay.original R Q roster b spring t t m j N start le_rfl away front atEdge
    φ X B y z gap o pos amp caps clear separated
  have funded:1 ≤ now:=(window R t j (j+1) start (away.trans front) (Nat.le_succ _)).1
  have f0 (s:I):0 ≤ fee (Q s) e (X s):=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have b0 (s:I):0 ≤ B s:=(amp s).1
  have ap (s:I):0 ≤ A s:=mul_nonneg (zero_le_one.trans ((C s).purchase funded)) (f0 s)
  have tz:1 ≤ T:=pace_ge _ away
  have zp:0 ≤ z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
  have paid:D.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*L^((∑s,l s)+(∑s,w s)) ≤ bill:=by simp [bill,w,k,l,capP,asp]
  have rates:=sold R older m j N (start.trans away) front atEdge.le l w A B era T gap z bill
    tz pos zp ap b0 paid issued.1 (by simpa only [Nat.add_zero] using issued.2)
  have rent:=WilsonIndependentConditionedPivotTailTwoFees.original R D S C k gain k t m j start away front
    (fun s=>fee (Q s) e (X s)) B z gap T (Q 0).h f0 b0 zp pos (zero_le_one.trans tz)
  have diff:((b:ℝ)-((∑s,l s:ℕ):ℝ))=(gain:ℝ):=by change (((capP Q+gain:ℕ):ℝ)-(capP Q:ℝ))=(gain:ℝ);push_cast;ring
  simp only [w,Finset.sum_const_zero,Nat.cast_zero,zero_div,Real.rpow_zero,mul_one,diff,Real.rpow_natCast,Nat.add_zero] at rates
  exact ⟨rates.1,rates.2.1.trans rent,fun q hq a ha=>(rates.2.2 q hq a ha).more rent⟩

end YM.Integration.WilsonIndependentConditionedPivotTailTwoEdge

