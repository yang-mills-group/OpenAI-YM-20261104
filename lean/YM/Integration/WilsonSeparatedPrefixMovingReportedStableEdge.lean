import YM.Integration.WilsonSeparatedPrefixMovingReportedStableLane
import YM.Integration.WilsonIndependentConditionedPivotTailTwoEdge
import YM.Integration.WilsonIndependentConditionedPivotTailTwoDay
import YM.Integration.WilsonIndependentConditionedPivotTailTwoFees
import YM.Integration.WilsonIndependentMovingRosterStableRetention

/-! A complete first union on the genuine earlier read. Its local moment is
the sum of the filed grades plus the gain; the upper cutoff only labels the
inherited vacuum and the actual dated operands. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingReportedStableEdge
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


open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMovingRosterStableMoney (fees)

def born (R:Realm G (e+1) E)(m j N:ℕ)(l:I→ℕ)(P:I→ℕ→Era G ℝ):Era G ℝ:=
  DeltaGap R.draws R.paid j N (fun s=>P s (j+1-m)) l
def stored (R:Realm G (e+1) E)(m j N:ℕ)(l:I→ℕ)(P:I→ℕ→Era G ℝ):Era G ℝ:=
  cruises R.draws R.paid N (∑s,l s) j m (born R m j N l P)
def tuition (k e b:ℕ)(gap z:ℝ)(A B:I→ℝ):ℝ:=
  profiles (n+1) k e 0 b gap z (∏s,factor 0 b z*(B s*A s))

theorem original {D:Fin ((n+1)+1)→ℕ}(G:Gauge)(e gain k:ℕ)(d l:I→ℕ)(E W V:Credit):
    let b:=(∑s,d s)+gain
    ∃C:Credit,∀(R:Realm G (e+1) E)(_spring:SpringD R k 0 b W)(_later:Dormitory R (∑s,l s) 0 V)
    (m j K N:ℕ),R.anchor ≤ m → m ≤ j → j<K → K ≤ N → (∑s,l s) ≤ k →
    ∀(φ:(s:I)→Rarity (D s))(A B:I→ℝ)(y z gap:ℝ)(o:CellR)(w:I→ℕ)(P:I→ℕ→Era G ℝ),
    (∀s,0 ≤ A s) → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 y ≤ z) → 0<gap →
    (∀a c:Fin (n+1),a≠c→ClearDay (φ a.succ) (φ c.succ) gap) →
    (∀a:Fin (n+1),∀p∈tsupport (φ a.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p q) →
    (∀s,Lane R (l s) (d s) m (K-m) N 0 b (φ s) y o (paceT R.draws.S m K)
      ((w s:ℝ)/4) (A s) (B s) (P s)) →
    Auth (∑s,l s) (stored R m j N l P) ∧ Flush e 0 1 (stored R m j N l P)
      (C.buy (epoch R m (j+1))*(paceT R.draws.S m (j+1))^gain*tuition k e b gap z A B):=by
  intro b
  let rank:=∑s,l s
  let size:=∑s,d s
  let S:=priceWG G e k 0 b E W
  let own:=fun _:I=>Credit.unit
  obtain ⟨C,carry⟩:=WilsonIndependentMovingRosterStableRetention.original (n:=n) G rank k e 0 b E W V
  refine ⟨WilsonIndependentConditionedPivotTailTwoFees.total C S E b own,?_⟩
  intro R spring later m j K N start base edge last room φ A B y z gap o w P a0 amp caps apart separated far lanes
  let zero:=fun _:I=>(0:ℕ)
  let L:ℝ:=(ll R.draws j).L.val
  let bill:=C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*L^size
  let r:=paceT R.draws.S m (j+1)
  let δ:=paceT R.draws.S m N
  have home₀ (s:I):homes m m s=m:=Fin.cases rfl (fun _=>rfl) s
  have center₀ (s:I):centers y 1 s=y:=Fin.cases (by simp [WilsonIndependentMovingRosterStableSale.centers]) (fun _=>rfl) s
  have fee₀ (s:I):fees 0 b d zero A B z δ r 1 s=
      WilsonIndependentMatchedRosterTariff.offer 0 b (d s) 0 z δ r (A s) (B s):=by
    induction s using Fin.cases with
    | zero=>simp [fees,zero]
    | succ a=>rfl
  have sold:=WilsonIndependentConditionedPivotTailLocalSale.original R spring m m le_rfl base (edge.trans_le last)
    (start.trans base) l d zero room φ A B y z gap o P
  simp only [pace_self,home₀,center₀,one_smul,one_pow,one_mul,zero_add,Nat.add_zero] at sold
  have lanes' (s:I):OnEdge R (l s) 0 b m N j (φ s) y o (P s) (fees 0 b d zero A B z δ r 1 s):=by
    rw [fee₀]
    exact WilsonSeparatedPrefixMovingReportedStableLane.gross R base edge (φ s) y z o (A s) (B s) (P s)
      (a0 s) (amp s) (caps s) (lanes s)
  have spend:=sold le_rfl apart a0 amp caps separated far lanes'
  have b0 (s:I):0 ≤ B s:=(amp s).1
  have z0:0 ≤ z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
  have paid:C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*L^((∑s,d s)+(∑s,zero s)) ≤ bill:=by
    simp [bill,zero,size]
  have rates:=carry R later m j N start base (edge.le.trans last) d zero A B (born R m j N l P) 1 gap z bill
    le_rfl apart z0 a0 b0 paid spend.1 (by simpa only [born,Nat.add_zero,one_pow,one_mul] using spend.2)
  have total:=WilsonIndependentConditionedPivotTailTwoFees.original (n:=n) R C S own size gain k m m j start le_rfl base
    A B z gap 1 (d 0) a0 b0 z0 apart zero_le_one
  have one (x:ℝ):Credit.unit.buy x=1:=by simp [Credit.unit,Credit.buy]
  simp only [own,one,one_pow,one_mul] at total
  have diff:(b:ℝ)-((∑s,d s:ℕ):ℝ)=(gain:ℝ):=by dsimp only [b];push_cast;ring
  simp only [zero,Finset.sum_const_zero,Nat.cast_zero,zero_div,Real.rpow_zero,mul_one,diff,
    Real.rpow_natCast,one_pow,one_mul] at rates
  exact ⟨rates.1,rates.2.1.trans total,fun q hq a ha=>(rates.2.2 q hq a ha).more total⟩
end YM.Integration.WilsonSeparatedPrefixMovingReportedStableEdge
