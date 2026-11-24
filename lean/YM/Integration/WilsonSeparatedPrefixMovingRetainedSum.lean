import YM.Integration.WilsonSeparatedPrefixMovingReportedStableLaw
import YM.Integration.WilsonSeparatedPrefixMovingRetainedEdge
import YM.Integration.WilsonSeparatedPrefixMovingRetainedCalendar
import YM.Integration.WilsonSeparatedPrefixMovingReportedStableSum
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
namespace YM.Integration.WilsonSeparatedPrefixMovingRetainedSum
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

open private combine from YM.Integration.WilsonSeparatedPrefixMovingReportedStableSum
open WilsonSeparatedPrefixMovingRetainedEdge (discounted)
open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonSeparatedPrefixMovingReportedStableEdge (stored tuition)
/-- The genuine earned price on the same source supplies one ratio for each stable arm. -/
theorem tuition_split (out e b:ℕ)(gap z:ℝ)(δ x:ℝ)(dp:0<δ)(xp:0<x)(w:I→ℕ)(A B:I→ℝ):
    tuition out e b gap z (discounted δ x w A) B=
      tuition out e b gap z A B*(δ/x)^(((∑s,w s:ℕ):ℝ)/4):=by
  have h (s:I):factor 0 b z*(B s*discounted δ x w A s)=
      (factor 0 b z*(B s*A s))*(δ/x)^((w s:ℝ)/4):=by unfold discounted;ring
  simp only [tuition,profiles,h,Finset.prod_mul_distrib,←Real.rpow_sum_of_pos (div_pos dp xp),
    ←Finset.sum_div,←Nat.cast_sum,mul_assoc]

theorem ratio (δ x:ℝ)(dp:0<δ)(xp:0<x)(gain:ℕ)(a:ℝ):
    x^gain*(δ/x)^a=δ^a*x^((gain:ℝ)-a):=by
  rw [Real.div_rpow dp.le xp.le,Real.rpow_sub xp,Real.rpow_natCast]
  ring

theorem original {D:Fin ((n+1)+1)→ℕ}(G:Gauge)(e gain out:ℕ)(d l:I→ℕ)(E W V:Credit):
    let b:=(∑s,d s)+gain
    ∃C:Credit,∀(R:Realm G (e+1) E)(_spring:SpringD R out 0 b W)(_later:Dormitory R (∑s,l s) 0 V)
    (m H K N:ℕ),R.anchor ≤ m → m ≤ H → H ≤ K → K ≤ N → (∑s,l s) ≤ out →
    ∀(φ:(s:I)→Rarity (D s))(A B:I→ℝ)(y z gap:ℝ)(o:CellR)(w:I→ℕ)(P:I→ℕ→Era G ℝ),
    3/2 ≤ (gain:ℝ)-((∑s,w s:ℕ):ℝ)/4 →
    (∀s,0 ≤ A s) → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 y ≤ z) → 0<gap →
    (∀a c:Fin (n+1),a≠c→ClearDay (φ a.succ) (φ c.succ) gap) →
    (∀a:Fin (n+1),∀p∈tsupport (φ a.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p q) →
    (∀s,Lane R (l s) (d s) m (K-m) N 0 b (φ s) y o (paceT R.draws.S m K)
      ((w s:ℝ)/4) (A s) (B s) (P s)) →
    let Δ:=reading R m K N l P-reading R m H N l P
    let pay:=2*C.buy (epoch R m H)*(paceT R.draws.S m H)^((gain:ℝ)-((∑s,w s:ℕ):ℝ)/4)*
      (paceT R.draws.S m K)^(((∑s,w s:ℕ):ℝ)/4)*tuition out e b gap z A B
    Auth (∑s,l s) Δ ∧ Flush e 0 1 Δ pay ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖Δ.2 q 0 ω‖ ≤ pay:=by
  intro b
  obtain ⟨C,edge⟩:=WilsonSeparatedPrefixMovingRetainedEdge.original (D:=D) G e gain out d l E W V
  refine ⟨WilsonSeparatedPrefixMovingRetainedCalendar.reserve C,?_⟩
  intro R spring dorm m H K N start base cut prior level φ A B y z gap o w P surplus amount tests caps apart near far lanes Δ pay
  let U:=tuition out e b gap z A B
  let v:ℝ:=((∑s,w s:ℕ):ℝ)/4
  let δ:=paceT R.draws.S m K
  let units (a:ℕ):=C.buy (epoch R m (H+a+1))*(paceT R.draws.S m (H+a+1))^((gain:ℝ)-v)
  let rows (a:ℕ):=stored R m (H+a) N l P
  have head (s:I)(a:ℕ)(ha:a ≤ K-m):Auth (l s) (P s a):=(lanes s).accounts.head a ha
  have steps (s:I)(a:ℕ)(ha:a<K-m):verseI R.draws R.paid (m+a) N (l s) (P s (a+1))=P s a:=(lanes s).pushed a ha
  have printed:Δ=∑a∈Finset.range (K-H),rows a:=WilsonSeparatedPrefixMovingReportedStableLaw.original R m H K N
    base cut prior l P head steps
  have joined:=combine (Finset.range (K-H)) rows (fun a=>units a*(δ^v*U)) (e:=e) (k:=∑s,l s) (by
    intro a ha
    have ordered:H+a<K:=by have hi:=Finset.mem_range.mp ha;omega
    have hit:=edge R spring dorm m (H+a) K N start (base.trans (Nat.le_add_right ..)) ordered prior level
      φ A B y z gap o w P amount tests caps apart near far lanes
    let x:=paceT R.draws.S m (H+a+1)
    have price:C.buy (epoch R m (H+a+1))*x^gain*tuition out e b gap z (discounted δ x w A) B=
        units a*(δ^v*U):=by
      rw [tuition_split out e b gap z δ x (pace_pos ..) (pace_pos ..)]
      change _=C.buy (epoch R m (H+a+1))*x^((gain:ℝ)-v)*(δ^v*U)
      change C.buy (epoch R m (H+a+1))*x^gain*(U*(δ/x)^v)=_
      calc
        _=C.buy (epoch R m (H+a+1))*(x^gain*(δ/x)^v)*U:=by ring
        _=_:=by rw [ratio δ x (pace_pos ..) (pace_pos ..) gain v];ring
    exact ⟨hit.1,price ▸ hit.2⟩)
  have good:0 ≤ U:=by
    have zp:0 ≤ z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
    have co:0 ≤ coinMat out e+1:=by linarith only [coinMat_nn out e]
    have prod:0 ≤ ∏s,factor 0 b z*(B s*A s):=by
      apply Finset.prod_nonneg
      intro s _
      exact mul_nonneg (by unfold WilsonIndependentMatchedRosterTariff.factor;positivity) (mul_nonneg (tests s).1 (amount s))
    dsimp only [U,tuition,profiles];positivity
  have fee:(∑a∈Finset.range (K-H),units a*(δ^v*U)) ≤ pay:=by
    rw [←Finset.sum_mul]
    have calendar:=WilsonSeparatedPrefixMovingRetainedCalendar.original R C m H (K-H) start base ((gain:ℝ)-v) surplus
    have total:=mul_le_mul_of_nonneg_right calendar (mul_nonneg (Real.rpow_nonneg (pace_pos R.draws.S m K).le v) good)
    exact total.trans_eq (by dsimp only [pay,v,δ,U];ring)
  rw [←printed] at joined
  have paid:Flush e 0 1 Δ pay:=⟨joined.2.1.trans fee,fun q hq a ha=>(joined.2.2 q hq a ha).more fee⟩
  exact ⟨joined.1,paid,WilsonIndependentMatchedCoverJoined.unit paid⟩
end YM.Integration.WilsonSeparatedPrefixMovingRetainedSum
