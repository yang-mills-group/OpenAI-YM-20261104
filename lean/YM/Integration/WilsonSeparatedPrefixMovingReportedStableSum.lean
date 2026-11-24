import YM.Integration.WilsonSeparatedPrefixMovingReportedStableLaw
import YM.Integration.WilsonSeparatedPrefixMovingReportedStableEdge
import YM.Integration.WilsonIndependentConditionedPivotTailTwo
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
namespace YM.Integration.WilsonSeparatedPrefixMovingReportedStableSum
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

private theorem combine {e k:ℕ}{ι:Type*}(s:Finset ι)(D:ι→Era G ℝ)(w:ι→ℝ)
    (paid:∀i∈s,Auth k (D i) ∧ Flush e 0 1 (D i) (w i)):
    Auth k (∑i∈s,D i) ∧ Flush e 0 1 (∑i∈s,D i) (∑i∈s,w i):=by
  refine ⟨Auth.sum fun i hi=>(paid i hi).1,?_⟩
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty];exact ⟨le_rfl,fun _ _ _ _=>Fruit.zero⟩
  | @insert i s new earlier=>
    have item:=(paid i (Finset.mem_insert_self i s)).2
    have rest:=earlier (fun j hj=>paid j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert new,Finset.sum_insert new]
    exact ⟨add_nonneg item.1 rest.1,fun q hq l hl=>(item.2 q hq l hl).plus (rest.2 q hq l hl) zero_le_one⟩


open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonSeparatedPrefixMovingReportedStableEdge (stored tuition)
theorem original {D:Fin ((n+1)+1)→ℕ}(G:Gauge)(e gain out:ℕ)(d l:I→ℕ)(E W V:Credit)(surplus:2 ≤ gain):
    let b:=(∑s,d s)+gain
    ∃C:Credit,∀(R:Realm G (e+1) E)(_spring:SpringD R out 0 b W)(_later:Dormitory R (∑s,l s) 0 V)
    (m H K N:ℕ),R.anchor ≤ m → m ≤ H → H ≤ K → K ≤ N → (∑s,l s) ≤ out →
    ∀(φ:(s:I)→Rarity (D s))(A B:I→ℝ)(y z gap:ℝ)(o:CellR)(w:I→ℕ)(P:I→ℕ→Era G ℝ),
    (∀s,0 ≤ A s) → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 y ≤ z) → 0<gap →
    (∀a c:Fin (n+1),a≠c→ClearDay (φ a.succ) (φ c.succ) gap) →
    (∀a:Fin (n+1),∀p∈tsupport (φ a.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p q) →
    (∀s,Lane R (l s) (d s) m (K-m) N 0 b (φ s) y o (paceT R.draws.S m K)
      ((w s:ℝ)/4) (A s) (B s) (P s)) →
    let Δ:=reading R m K N l P-reading R m H N l P
    let pay:=2*C.buy (epoch R m H)*(paceT R.draws.S m H)^gain*tuition out e b gap z A B
    Auth (∑s,l s) Δ ∧ Flush e 0 1 Δ pay ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖Δ.2 q 0 ω‖ ≤ pay:=by
  intro b
  obtain ⟨C,edge⟩:=WilsonSeparatedPrefixMovingReportedStableEdge.original (D:=D) G e gain out d l E W V
  refine ⟨C.finances 1 le_rfl,?_⟩
  intro R spring dorm m H K N start base cut prior level φ A B y z gap o w P amount tests caps apart near far lanes Δ pay
  let U:=tuition out e b gap z A B
  let units (a:ℕ):=C.buy (epoch R m (H+a+1))*(paceT R.draws.S m (H+a+1))^gain
  let rows (a:ℕ):=stored R m (H+a) N l P
  have head (s:I)(a:ℕ)(ha:a ≤ K-m):Auth (l s) (P s a):=(lanes s).accounts.head a ha
  have steps (s:I)(a:ℕ)(ha:a<K-m):verseI R.draws R.paid (m+a) N (l s) (P s (a+1))=P s a:=(lanes s).pushed a ha
  have printed:Δ=∑a∈Finset.range (K-H),rows a:=WilsonSeparatedPrefixMovingReportedStableLaw.original R m H K N
    base cut prior l P head steps
  have joined:=combine (Finset.range (K-H)) rows (fun a=>units a*U) (e:=e) (k:=∑s,l s) (by
    intro a ha
    have ordered:H+a<K:=by have hi:=Finset.mem_range.mp ha;omega
    exact edge R spring dorm m (H+a) K N start (base.trans (Nat.le_add_right ..)) ordered prior level
      φ A B y z gap o w P amount tests caps apart near far lanes)
  have good:0 ≤ U:=by
    have zp:0 ≤ z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
    have co:0 ≤ coinMat out e+1:=by linarith only [coinMat_nn out e]
    have prod:0 ≤ ∏s,factor 0 b z*(B s*A s):=by
      apply Finset.prod_nonneg
      intro s _
      exact mul_nonneg (by unfold WilsonIndependentMatchedRosterTariff.factor;positivity) (mul_nonneg (tests s).1 (amount s))
    dsimp only [U,tuition,profiles];positivity
  have fee:(∑a∈Finset.range (K-H),units a*U) ≤ pay:=by
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (WilsonIndependentConditionedPivotTailCalendar.original R C m m H (K-H) gain start le_rfl base surplus) good
  rw [←printed] at joined
  have paid:Flush e 0 1 Δ pay:=⟨joined.2.1.trans fee,fun q hq a ha=>(joined.2.2 q hq a ha).more fee⟩
  exact ⟨joined.1,paid,WilsonIndependentMatchedCoverJoined.unit paid⟩
end YM.Integration.WilsonSeparatedPrefixMovingReportedStableSum
