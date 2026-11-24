import YM.Integration.WilsonIndependentConditionedLocalRate
import YM.Integration.WilsonIndependentMatchedRosterPlanted
import YM.Integration.WilsonIndependentConditionedMovingSeat
import YM.Integration.WilsonIndependentConditionedMovingReceiver

/-! The nonempty-mask first-join estimate on the actual N-vacuum with the marks born at K. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankAxes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count wallet entry)
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedPivotSeat (axis film ticket)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedRosterChronology (mass)
open WilsonIndependentMatchedRosterSlots (wallet entry degree count)
variable {G:Gauge}{n e k u₀:ℕ}{H:Hol G}
local notation "J" => Fin (n+1)
variable (Q:Fin (n+1)→SealR G)(own:∀i,Rails (Q i).h k u₀ e)
variable (E W K₀ U:Credit)
abbrev Cuts:= (i:J)→CutsP H (Q i).ans (Q i).path (own i) E W K₀ U

def allowance (X:Cuts (H:=H) Q own E W K₀ U)(flag:J→Bool)(A:J→ℝ)(u b:ℕ)(i:J):ℝ:=
  if flag i then A i else (tariff H (Q i).ans (Q i).path e u b E W U).buy (X i).Age

def inlet (X:Cuts (H:=H) Q own E W K₀ U)(flag:J→Bool)(a:J→ℝ)(j:(i:J)→Alma (Q i).F)
    (φ:(i:J)→Rarity (Q i).D)(y:ℝ)(o:CellR)(i:J):Era G ℝ:=
  if flag i then seat (X i) (a i) (φ i) y o (X i).i else film (X i) (j i) 0 (φ i) y o (X i).i

theorem original (E' W₀ U₀:Credit)(flag:J→Bool)(out u b:ℕ):
    ∃(S:J→Credit)(C S₀:Credit),
    let l:=fun i=>degree (flag i) k (Q i).h
    let hits:=∑i,count (flag i)
    ∀(ζ:ℝ)(R:Realm G (e+1) E')(X:Cuts (H:=H) Q own E W K₀ U)
      (host m K N:ℕ)(_old:R.anchor ≤ host)(_stop:host ≤ m)(_birth:m ≤ K)(_quiet:K ≤ N)
      (_files:∀i,(X i).ax=R.draws)(_reset:∀i,(X i).tx=R.paid)
      (_homes:∀i,(X i).m=m)(_cut:∀i,(X i).ceilC=K)(_vac:∀i,(X i).N=N)
      (a:J→ℝ)(j:(i:J)→Alma (Q i).F)(φ:(i:J)→Rarity (Q i).D)
      (y t z:ℝ)(o:CellR)(B:J→ℝ),
    let A:=fun i=>(S i).buy (X i).Age*(|a i| * (X i).fuel)
    let bill:=allowance Q own E W K₀ U X flag A u b
    let amt:=WilsonIndependentConditionedLocalRate.fee out e u b l t z bill B
      (C.buy (WilsonIndependentMatchedCoverDate.age R m K)) ((∑i,(Q i).h:ℕ):ℝ) ζ
    let rate:=(paceT R.draws.S m K)^ζ
    let due:=S₀.buy (WilsonIndependentMatchedCoverDate.age R host m)*(amt*rate)
    let field:=cruises R.draws R.paid N ((n+1)*k) K host (MassP G ℝ n (inlet Q own E W K₀ U X flag a j φ y o))
    (∑i,l i) ≤ out → ζ ≤ (hits:ℝ)/4 → ((∑i,(Q i).h:ℕ):ℝ)+ζ < b →
    SpringD R out u b W₀ → Dormitory R (∑i,l i) u U₀ → u+b ≤ u₀ →
    0<t → (∀i j,i≠j→ClearDay (φ i) (φ j) t) → (∀i,radiusH (φ i) 1 y ≤ z) →
    (∀i,Amplitude (φ i) (B i)) →
    response e u field due:=by
  classical
  choose S bought using fun i=>WilsonIndependentConditionedMovingSalary.original H (Q i).ans (Q i).path (own i) E W K₀ U
  let l:=fun i=>degree (flag i) k (Q i).h
  obtain ⟨C,sale⟩:=WilsonIndependentConditionedLocalRate.original (G:=G) (E:=E') (e:=e)
    (dim:=fun i=>(Q i).D) l (fun i=>(Q i).h) (fun i=>count (flag i)) out u b W₀ U₀
  obtain ⟨S₀,receive⟩:=WilsonIndependentConditionedMovingReceiver.original G (∑i,l i) e u E' U₀
  refine ⟨S,C,S₀,?_⟩
  intro _ hits ζ R X host m K N old stop birth quiet files reset homes cut vac a j φ y t z o B A bill amt rate due field room release clear spring dorm width ht sep bound tests
  have same:m+(K-m)=K:=by omega
  have pos (i:J):0 ≤ A i:=by
    have hS:=zero_le_one.trans ((S i).purchase (X i).windowC.warm)
    exact mul_nonneg hS (mul_nonneg (abs_nonneg _) (X i).hf)
  let directions (i:J):Verse (Q i).F:=axis (j i) 0
  let P (i:J):=entry (flag i) (X i) (a i) (directions i) (φ i) y o
  have slot i:=WilsonIndependentConditionedMovingSeat.original (X i) R (files i) (reset i) (homes i) (cut i) (vac i)
    (flag i) (a i) (directions i) (φ i) y o (A i) (B i) (tests i) u b width (pos i) (bought i (X i) (a i))
  have billEq (i:J):wallet (flag i) (X i) (directions i) (A i) u b=bill i:=by
    dsimp only [bill,allowance,directions,wallet]
    cases flag i <;> simp [ticket (j i) 0 (Nat.zero_le e)]
  have member(i:J):0 ≤ bill i ∧ WilsonIndependentMatchedRosterLane.Lane R (l i) (Q i).h m (K-m) N u b (φ i) y o
      (paceT R.draws.S m K) ((count (flag i):ℝ)/4) (bill i) (B i) (P i):=by
    rw [←billEq i]
    exact ⟨(slot i).1,(slot i).2.1⟩
  have localFee:=sale ζ R m (K-m) N (old.trans stop) (by omega) φ P y t z o bill B room release clear spring dorm ht sep bound
    (fun i=>(member i).1) tests (fun i=>by rw [same];exact (member i).2)
  rw [same] at localFee
  have done:=receive R dorm host m K N old stop birth quiet (mass P (K-m)) (amt*rate) localFee.1 localFee.2
  have smaller:(∑i,l i) ≤ (n+1)*k:=by
    have h(i:J):l i ≤ k:=by cases hd:flag i <;> simp [l,degree,hd,(own i).hk]
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>h i)
  have empty:Auth (∑i,l i) (mass P (K-m)):=manCo _ l (fun i=>(member i).2.accounts.head _ le_rfl)
  have widen:=WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green (stop.trans birth) quiet _ empty smaller
  have placed:mass P (K-m)=MassP G ℝ n (inlet Q own E W K₀ U X flag a j φ y o):=by
    apply congrArg (MassP G ℝ n)
    funext i
    have position:K-m=(X i).i:=by have v:(X i).m+(X i).i=K:=cut i;have h:=homes i;omega
    dsimp only [P,WilsonIndependentMatchedRosterSlots.entry,inlet]
    rw [position]
    cases flag i <;> rfl
  dsimp only [field]
  rw [←placed,←widen]
  exact done.2

end YM.Integration.WilsonIndependentConditionedBankAxes
