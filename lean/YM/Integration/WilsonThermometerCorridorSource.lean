import YM.Integration.WilsonThermometerCorridorActors
import YM.Integration.WilsonThermometerCorridorBirth
import YM.Integration.WilsonThermometerCorridorAffine
import YM.Integration.WilsonThermometerWeakMixedCapture

/- The two true taps of the complete named separated incoming R gallery at
   its exact reference f use the affordable rides from the earlier grouped
   date. The continuation below f has the same actors on every original mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorSource
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "slots" => (Stock.census (Fin 3))

local notation "CF"=>R.family

open RG05Readout.Pantry WilsonThermometerOwnOffsetJoint

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cater:Cater (CF) R.doors)(t:ℕ)(ht:1≤t):
    ∀ᶠ b:ℕ in atTop,∀ m N p (_:b ≤ m)(edge:m+1<N)(o:Fin 3→Site ((CF).side N p))
      (V:(i:Fin 3)→Sight (CF) (d i) p)(Q:(i:Fin 3)→Emblems (CF) (d i))
      (_:∀i,Enrolled R.makes R.doors (B) (m+1) N p (d i) (digits R N p (o i)) (V i) (Q i))
      (y:(i:Fin 3)→Palette (CF) (d i)),
      let z:=fun i=>WilsonThermometerMarchSource.reduce (y i)
      let P:=(CF).path.rep N p (m+1)
      let w:=radius R t b (m+1)
      let X:=WilsonThermometerIntrinsicRoster.density R d o z Q slots edge.le edge.le
      WilsonThermometerIntrinsicRoster.filed R d o z V Q slots edge.le t →
      ∀D:ℕ,(∀i i':Fin 3,i≠i'→D*(4*P.p.B+2)+2*P.p.B < separation (origins R o (m+1) i) (origins R o (m+1) i')) →
      0<w ∧ w⁻¹≤β (m+1)^(t+(m+1-b)) ∧
      ∃ (actors:∀j,Fin 3→Three G ((CF).side j p))(coins:ℕ→Fin 3→ℝ)(Z:Config G ((CF).side (m+1) p) → Poly (census slots)),
        (∀j,m+1≤j → j≤N → ∀i,actors j i=state (k:=m+1) R (V i) (Q i) (z i) (o i) j) ∧
        (∀j,b≤j → ∀jf:j < m+1,∀i,Ride ((A).clock.op j p) (origins R o (j+1) i)
          (origins R o j i) (R.doors N p j (jf.trans edge)) 1 (actors (j+1) i) (actors j i) (coins j i)) ∧
        (∀ j,b≤j → j < m+1 → ∀i,0≤coins j i ∧ 2*w*coins j i≤1) ∧
        MenuBoard P (liveRow (actors (m+1))) Z (origins R o (m+1) ∘ Prod.fst)
          (fun _=>w) (((A).budget (m+1)).supportExponent-1) 1 ∧
        (∀ U,specialize slots ((Real.exp (-(D:ℝ)):ℝ):ℂ) (Z U)=X U) ∧
        (∀ U,specialize slots 0 (Z U)=restore P (fun i=>(actors (m+1) i).2.1)
          (fun i=>profile P.activities (actors (m+1) i).2.2)
          (0:Support ((CF).side (m+1) p) → Config G ((CF).side (m+1) p) → Poly slots) 0 U) ∧
        (∀U,WilsonThermometerMixedAmplitude.Line ((Real.exp (-(D:ℝ)):ℝ):ℂ)
          (specialize slots 0 (Z U)) (specialize slots ((Real.exp (-(D:ℝ)):ℝ):ℂ) (Z U))
          (specialize slots 1 (Z U))):=by
  filter_upwards [WilsonThermometerCorridorActors.original R simple shop t ht,(A).fits.deep.eventually_ge_atTop 4]
    with b pupils four m N p bm edge o V Q tracks y
  dsimp only
  intro filed D far
  have bf:=bm.trans m.le_succ
  obtain ⟨wpos,small,cash,actors,coins,same,rides,fees⟩:=pupils (m+1) N p bf edge.le o V Q tracks y
  let z:=fun (i:Fin 3)=>WilsonThermometerMarchSource.reduce (y i)
  let top:=(CF).path.rep N p (m+1)
  let raw:=fun (i:Fin 3)=>state (k:=m+1) R (V i) (Q i) (z i) (o i) (m+1)
  let X:=WilsonThermometerIntrinsicRoster.density R d o z Q slots edge.le edge.le
  let w:=radius R t b (m+1)
  have agree:actors (m+1)=raw:=funext (same (m+1) le_rfl edge.le)
  have grant:=(WilsonThermometerWeakMixedMenu.original R y filed (le_refl (m+1)) edge.le far).1
  rw [topPitch,if_neg edge.ne] at grant
  have grant':Served top (fun i=>(actors (m+1) i).2.1) (fun i=>profile top.activities (actors (m+1) i).2.2)
      X (origins R o (m+1)) (fun _=>radius R t (m+1) (m+1)) (((A).budget (m+1)).supportExponent-1)
      (Real.exp (-(D:ℝ))):=by rw [agree];exact grant
  have occupy:Occupancy (origins R o (m+1) ∘ (Prod.fst:Fin 3×Bool→Fin 3)) (apron (A) m):=by
    intro v
    refine (Finset.card_le_univ _).trans ?_
    have soon:4≤(A).clock.J (m+1):=four.trans ((A).fits.mono bf)
    change Fintype.card (Fin 3×Bool) ≤ ((A).clock.J (m+1)+2)*((CF).S.block m).val^4
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    calc 3*2 ≤ (A).clock.J (m+1)+2 :=by omega
         _ ≤ _:= Nat.le_mul_of_pos_right _ (pow_pos ((CF).S.block m).property 4)
  have r (i:Fin 3):Ride ((A).clock.op m p) (origins R o (m+1) i)
      (((A).clock.op m p).ratio.parent (origins R o (m+1) i))
      (R.doors N p m (show m<N by omega)) 1 (actors (m+1) i) (actors m i) (coins m i):=by
    rw [WilsonThermometerOwnOffsetGeometry.parent R o (show m<N by omega) i]
    exact rides m bm m.lt_succ_self i
  obtain ⟨Z,board,physical,removed,H,K,chart,kept⟩:=WilsonThermometerCorridorBirth.retained R cater
    (show m<N by omega) (actors (m+1)) (actors m) X (origins R o (m+1))
    (fun _=>w) (fun _=>radius R t (m+1) (m+1)) (coins m) (Real.exp_pos _)
    (fun _=>wpos) (fun _=>small) r occupy (fun i=>(fees m bm m.lt_succ_self i).2) grant'
  exact ⟨wpos,cash,actors,coins,Z,same,rides,fees,board,physical,removed,fun U=>by
    rw [kept]
    exact WilsonThermometerCorridorAffine.original _ _ _ (Real.exp_pos _) H K chart U⟩

end YM.Integration.WilsonThermometerCorridorSource
end
