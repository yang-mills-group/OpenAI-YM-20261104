import YM.Integration.WilsonThermometerWeakMixedBoard
import YM.Integration.WilsonThermometerCorridorWalk

/- Keep the already deposited, jointly named complete Wilson numerator at f.
   Its two tagged pronunciations are put on the very same original hard gallery,
   at the smaller radius paid by the three genuine lower physical rides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorBirth
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonThermometerOwnOffsetNectar
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C"=>R.family
local notation "A"=>R.family.path.levels
local notation "J"=>Stock.census I

private theorem narrow {n:Side}{E:Type}{F:E → Config G n→Poly (J)}{S:E→Support n}
    {w w₀:I→ℝ}{B:ℕ}{e δ:ℝ}(before:Towed w₀ S F B e δ)(cut:∀i,w i≤w₀ i)(wp:∀i,0<w i):
    Towed w S F B e δ:=by
  obtain ⟨dues,sums,hit,terms⟩:=before
  refine ⟨dues,sums,hit,?_⟩
  intro i
  obtain ⟨a,an,maj,paid⟩:=terms i
  refine ⟨a,an,maj,le_trans ?_ paid⟩
  unfold wordsPrice
  exact Finset.sum_le_sum (fun s _=>mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod (fun v _=>(wp v).le) (fun v _=>cut v)) (an s))

theorem retained (cater:Cater (C) R.doors){N p j:ℕ}(jn:j<N)
    (raw:I→Three G ((C).side (j+1) p))(down:I→Three G ((C).side j p))
    (X:Config G ((C).side (j+1) p)→Poly (J))(o:I→Site ((C).side (j+1) p))
    (w w₀ fee:I→ℝ){δ:ℝ}(slope:0<δ)(wp:∀i,0<w i)(cut:∀i,w i≤w₀ i)
    (rides:∀i,Ride ((A).clock.op j p) (o i) (((A).clock.op j p).ratio.parent (o i))
      (R.doors N p j jn) 1 (raw i) (down i) (fee i))
    (vacant:Occupancy (o ∘ (Prod.fst:I×Bool→I)) (apron (A) j))
    (cap:∀i,2*w i*fee i≤1):
    let P:=(C).path.rep N p (j+1)
    let e:=((A).budget (j+1)).supportExponent-1
    Served P (fun i=>(raw i).2.1) (fun i=>profile P.activities (raw i).2.2) X o w₀ e δ →
    ∃ Z,MenuBoard P (liveRow raw) Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 ∧
      (∀U,specialize (J) (δ:ℂ) (Z U)=X U) ∧
      (∀U,specialize (J) 0 (Z U)=restore P (fun i=>(raw i).2.1)
        (fun i=>profile P.activities (raw i).2.2)
        (0:Support ((C).side (j+1) p) → Config G ((C).side (j+1) p) → Poly (J)) 0 U) ∧
      ∃ H K,Carton o H K P.p.threshold ∧
        Z=WilsonMixedTaggedStart.lifted (R:=P) (fun i=>(raw i).2.1)
          (fun i=>profile P.activities (raw i).2.2) δ H K:=by
  intro P e before
  obtain ⟨H,K,chart,hH,hK,values⟩:=before
  let Φ:=fun i=>(raw i).2.1
  let κ:=fun i=>profile P.activities (raw i).2.2
  let Z:=WilsonMixedTaggedStart.lifted (R:=P) Φ κ δ H K
  have together:=WilsonMixedTaggedStart.represented Φ κ slope chart (narrow hH cut wp) (narrow hK cut wp)
  have clean:(fun i=>(liveRow raw i).2.1)=liveRow Φ:=by funext ⟨i,bit⟩;cases bit <;> rfl
  have hard:(fun i=>profile P.activities (liveRow raw i).2.2)=liveRow κ:=by
    funext ⟨i,bit⟩;cases bit
    · rfl
    · funext Y U;simp [liveRow,profile,cram]
  obtain ⟨a,f,course,_⟩:=cater.tiers j N p jn
  refine ⟨Z,?_,fun U=>(WilsonMixedTaggedStart.endpoints Φ κ slope chart U).1.trans (congrFun values U).symm,
    fun U=>(WilsonMixedTaggedStart.endpoints Φ κ slope chart U).2,H,K,chart,rfl⟩
  have served:Served P (fun i=>(liveRow raw i).2.1) (fun i=>profile P.activities (liveRow raw i).2.2)
      Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1:=by rw [clean,hard];exact together
  exact WilsonAllDateHarvestEndpointIntegrability.original (N:=N) (p:=p) (m:=j)
    (I:=liveRow raw) (Q:=liveRow down) (l:=liveRow fee) (o:=o ∘ Prod.fst) (w:=w ∘ Prod.fst)
    course R.makes.wilson jn (fun i=>wp i.1) (WilsonMixedTaggedRide.doubled rides) vacant
    (WilsonMixedTaggedRide.room cap) served

theorem original (cater:Cater (C) R.doors){N p j:ℕ}(jn:j<N)
    (raw:I→Three G ((C).side (j+1) p))(down:I→Three G ((C).side j p))
    (X:Config G ((C).side (j+1) p)→Poly (J))(o:I→Site ((C).side (j+1) p))
    (w w₀ fee:I→ℝ){δ:ℝ}(slope:0<δ)(wp:∀i,0<w i)(cut:∀i,w i≤w₀ i)
    (rides:∀i,Ride ((A).clock.op j p) (o i) (((A).clock.op j p).ratio.parent (o i))
      (R.doors N p j jn) 1 (raw i) (down i) (fee i))
    (vacant:Occupancy (o ∘ (Prod.fst:I×Bool→I)) (apron (A) j))
    (cap:∀i,2*w i*fee i≤1):
    let P:=(C).path.rep N p (j+1)
    let e:=((A).budget (j+1)).supportExponent-1
    Served P (fun i=>(raw i).2.1) (fun i=>profile P.activities (raw i).2.2) X o w₀ e δ →
    ∃ Z,MenuBoard P (liveRow raw) Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 ∧
      (∀U,specialize (J) (δ:ℂ) (Z U)=X U) ∧
      (∀U,specialize (J) 0 (Z U)=restore P (fun i=>(raw i).2.1)
        (fun i=>profile P.activities (raw i).2.2)
        (0:Support ((C).side (j+1) p) → Config G ((C).side (j+1) p) → Poly (J)) 0 U):=by
  intro P e before
  obtain ⟨Z,board,full,zero,_⟩:=retained R cater jn raw down X o w w₀ fee slope wp cut rides vacant cap before
  exact ⟨Z,board,full,zero⟩

end YM.Integration.WilsonThermometerCorridorBirth
end
