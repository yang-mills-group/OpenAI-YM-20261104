import YM.Integration.WilsonIndependentConditionedBankAxes
import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonIndependentMatchedRosterMasks

/-! Both orientations of the genuine axis probe and the two stable inputs share the entire pair, marked birth, inherited quiet and older read. Prices precede the positions and the finite cutoffs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairProbes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet present)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentConditionedBankAxes (Cuts allowance inlet)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open WilsonCoeffUV.Cosmos.Polestar
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u₀:ℕ}{H:Hol G}
local notation "J" => Fin 2
local notation "L₀" => Credit.leanC

structure Prices where
  slot : Bits 1 → Fin 2 → Credit
  window : Bits 1 → Credit
  stop : Bits 1 → Credit

variable (Q:J→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(E W K₀ U:Credit)

def reading (R:Realm G (e+1) L₀)(X:Cuts (H:=H) Q own E W K₀ U)(host K N:ℕ)
    (a:J→ℝ)(j:(i:J)→Alma (Q i).F)(φ:(i:J)→Rarity (Q i).D)(y:ℝ)(o:CellR)(mask:Bits 1):Era G ℝ:=
  cruises R.draws R.paid N (2*k) K host
    (MassP G ℝ 1 (inlet Q own E W K₀ U X (choose 1 mask) a j φ y o))

def charge (R:Realm G (e+1) L₀)(X:Cuts (H:=H) Q own E W K₀ U)(coins:Prices)(u b host m K:ℕ)
    (ζ:ℝ)(a B:J→ℝ)(t z:ℝ)(mask:Bits 1):ℝ:=
  let picked:=choose 1 mask
  let l:=fun i=>degree (picked i) k (Q i).h
  let A:=fun i=>(coins.slot mask i).buy (X i).Age*(|a i| * (X i).fuel)
  let bill:=allowance Q own E W K₀ U X picked A u b
  let amount:=WilsonIndependentConditionedLocalRate.fee (2*k) e u b l t z bill B
    ((coins.window mask).buy (WilsonIndependentMatchedCoverDate.age R m K)) ((∑i,(Q i).h:ℕ):ℝ) ζ
  (coins.stop mask).buy (WilsonIndependentMatchedCoverDate.age R host m)*(amount*(paceT R.draws.S m K)^ζ)

def Heard (R:Realm G (e+1) L₀)(coins:Prices)(u b:ℕ):Prop:=
  ∀(X:Cuts (H:=H) Q own E W K₀ U)(host m K N:ℕ),
    R.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
    (∀i,(X i).ax=R.draws) → (∀i,(X i).tx=R.paid) →
    (∀i,(X i).m=m) → (∀i,(X i).ceilC=K) → (∀i,(X i).N=N) →
    ∀(ζ:ℝ)(a:J→ℝ)(j:(i:J)→Alma (Q i).F)(φ:(i:J)→Rarity (Q i).D)
      (y t z:ℝ)(o:CellR)(B:J→ℝ),
    ζ≤1/4 → ((∑i,(Q i).h:ℕ):ℝ)+ζ < b → 0<t →
    (∀i j,i≠j→ClearDay (φ i) (φ j) t) → (∀i,radiusH (φ i) 1 y ≤ z) →
    (∀i,Amplitude (φ i) (B i)) →
    ∀mask:Bits 1,mask≠quiet 1 →
      response e u (reading Q own E W K₀ U R X host K N a j φ y o mask)
        (charge Q own E W K₀ U R X coins u b host m K ζ a B t z mask)

theorem names (R:Realm G (e+1) L₀)(X:Cuts (H:=H) Q own E W K₀ U)(host K N:ℕ)
    (a:J→ℝ)(j:(i:J)→Alma (Q i).F)(φ:(i:J)→Rarity (Q i).D)(y:ℝ)(o:CellR):
    let read:=reading Q own E W K₀ U R X host K N a j φ y o
    let Δ:=fun s:J=>seat (X s) (a s) (φ s) y o (X s).i
    let P:=fun s:J=>film (X s) (j s) 0 (φ s) y o (X s).i
    let hear:=cruises R.draws R.paid N (2*k) K host
    read (true,false)=hear (agateV (Δ 0) (P 1)) ∧ read (false,true)=hear (agateV (P 0) (Δ 1)) ∧
      read (true,true)=hear (agateV (Δ 0) (Δ 1)):=⟨rfl,rfl,rfl⟩

theorem rooms (u b:ℕ)(reserve:u+b≤u₀):
    ∃coins:Prices,∀(R:Realm G (e+1) L₀),SpringD R (2*k) u b L₀ →
      (∀l,l≤2*k→Dormitory R l u L₀) → Heard (H:=H) Q own E W K₀ U R coins u b:=by
  classical
  choose S C stop paid using fun mask:Bits 1=>WilsonIndependentConditionedBankAxes.original
    (H:=H) Q own E W K₀ U L₀ L₀ L₀ (choose 1 mask) (2*k) u b
  let coins:Prices:=⟨S,C,stop⟩
  refine ⟨coins,?_⟩
  intro R spring dorm X host m K N live later upper quietTop files reset homes birth top ζ a j φ y t z o B
    released clear ht split sizes tests mask nonempty
  let l:=fun i=>degree (choose 1 mask i) k (Q i).h
  have dim (i:J):l i≤k:=by cases h:choose 1 mask i <;> simp [l,degree,h,(own i).hk]
  have full:(∑i,l i)≤2*k:=by
    exact (Finset.sum_le_sum (s:=Finset.univ) (f:=l) (g:=fun _=>k) (fun i _=>dim i)).trans
      (le_of_eq (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]))
  obtain ⟨s,hit⟩:=present 1 mask nonempty
  have bill:1≤∑i,count (choose 1 mask i):=by
    have here:=Finset.single_le_sum (f:=fun i:J=>count (choose 1 mask i))
      (fun i _=>Nat.zero_le _) (Finset.mem_univ s)
    simpa only [hit,WilsonIndependentMatchedRosterSlots.count,if_true] using here
  have wage:ζ ≤ ((∑i,count (choose 1 mask i):ℕ):ℝ)/4:=
    released.trans (div_le_div_of_nonneg_right (by exact_mod_cast bill) (by norm_num))
  exact paid mask ζ R X host m K N live later upper quietTop files reset homes birth top a j φ y t z o B
    full wage clear spring (dorm _ full) reserve ht split sizes tests

theorem original (u b height seats:ℕ){J₀:Hol G}(M:Master J₀)(reserve:u+b≤u₀)
    (depth:2*k≤b)(capacity:b ≤ seats)(tests:u ≤ seats):
    ∃coins:Prices,∀(R:Realm G (e+1) L₀),Elected M R height seats →
      Heard (H:=H) Q own E W K₀ U R coins u b:=by
  obtain ⟨coins,paid⟩:=rooms (H:=H) Q own E W K₀ U u b reserve
  exact ⟨coins,fun R sold=>paid R (sold.spring (2*k) u b depth capacity tests)
    (fun l bound=>sold.dorm l u (bound.trans (depth.trans capacity)) tests)⟩

end YM.Integration.WilsonIndependentConditionedPairProbes
