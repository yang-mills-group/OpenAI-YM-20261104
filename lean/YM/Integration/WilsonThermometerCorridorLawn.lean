import YM.Integration.WilsonThermometerCorridorSource
import YM.Integration.WilsonThermometerWeakMixedCapture
import YM.Integration.WilsonThermometerMarchFaceTransport
/- The two true taps of the complete named separated incoming R gallery at
   its exact reference f use the affordable rides from the earlier grouped
   date. The continuation below f has the same actors on every original mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorLawn
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

open WilsonThermometerCorridorRoster

local notation "V"=>Unit×Fin 3
local notation "Y"=>Stock.census (V)

private theorem shrink {n:Side}{P:Rep G n}{raw:Fin 3→Three G n}{F:Config G n→Poly slots}
    {o:Fin 3→Site n}{w:Fin 3→ℝ}{e e':ℝ}(offered:MenuBoard P raw F o w e 1)(cut:e'≤e)(wp:∀i,0<w i):
    MenuBoard P raw F o w e' 1:=by
  obtain ⟨alive,live,H,K,chart,salary,forced,field⟩:=offered
  exact ⟨alive,live,H,K,chart,salary.shrink cut le_rfl wp,forced.shrink cut le_rfl wp,field⟩

theorem room {n:Side}(j:ℕ)(active:4≤(A).clock.J (j+1))(o:(V)→Site n):Occupancy o (apron (A) j):=by
  intro x
  refine (Finset.card_le_univ _).trans ?_
  change Fintype.card (Unit×Fin 3) ≤ ((A).clock.J (j+1)+2)*((CF).S.block j).val^4
  simp only [Fintype.card_prod,Fintype.card_unique,Fintype.card_fin,one_mul]
  calc 3 ≤ (A).clock.J (j+1)+2 :=by omega
       _ ≤ _ :=Nat.le_mul_of_pos_right _ (pow_pos ((CF).S.block j).property 4)

def field {n:Side}(z:ℂ)(Z:Config G n→Poly (census slots))(U:Config G n):Poly (Y):=
  lift (specialize slots z (Z U))

theorem original (simple:G.Simple)(cater:Cater (CF) R.doors){b f N p:ℕ}
    (first:0<b)(fn:f≤N)(active:4≤(A).clock.J b)(raw:∀j,Fin 3→Three G ((CF).side j p))
    (o:Fin 3→Site ((CF).side N p))(cost:ℕ→Fin 3→ℝ)
    {w:ℝ}(wp:0<w)(Z:Config G ((CF).side f p)→Poly (census slots))
    (offer:MenuBoard ((CF).path.rep N p f) (liveRow (raw f)) Z (origins R o f ∘ Prod.fst)
      (fun _=>w) (((A).budget f).supportExponent-1) 1)
    (rides:∀j,b≤j → ∀jf:j<f,∀i,Ride ((A).clock.op j p) (origins R o (j+1) i)
      (origins R o j i) (R.doors N p j (jf.trans_le fn)) 1 (raw (j+1) i) (raw j i) (cost j i))
    (paid:∀j,b≤j → j<f → ∀i,0≤cost j i ∧ 2*w*cost j i≤1):
    ∀z:ℂ,‖z‖≤1 → ∀j,b≤j → ∀jf:j≤f,∃wallet:(V)→ℝ,
      (∀i,0<wallet i ∧ wallet i≤w ∧ (wallet i)⁻¹≤β f^(6*(f-j))*w⁻¹) ∧
      MenuBoard ((CF).path.rep N p j) (raw j ∘ Prod.snd) (gust (CF).path N p f (field z Z) j jf)
        (origins R o j ∘ Prod.snd) wallet (((A).budget j).supportExponent-2) 1:=by
  intro z hz
  have law:=(R.makes.wilson.represents N p f fn).good
  have stated:=WilsonThermometerWeakMixedCapture.filed (P:=(CF).path.rep N p f) (raw:=raw f) (o:=origins R o f) (w:=fun _=>w) law offer (fun _=>wp) hz
  have copy:=admit ((CF).path.rep N p f) (shrink (e':=((A).budget f).supportExponent-2) stated (by linarith) (fun _=>wp)) law (fun _=>wp) (fun _=>wp) (fun _=>le_rfl)
  apply WilsonThermometerCorridorWalk.original R simple cater first fn
    (fun j=>raw j ∘ Prod.snd) (fun j=>origins R o j ∘ Prod.snd) (fun j=>cost j ∘ Prod.snd)
    (fun _=>w) (field z Z) copy (fun _=>wp)
  · intro j _ jf;funext i
    exact (WilsonThermometerOwnOffsetGeometry.parent R o (jf.trans_le fn) i.2).symm
  · intro j bj jf i;exact rides j bj jf i.2
  · intro j bj _
    have funded:=active.trans ((A).fits.mono (bj.trans j.le_succ))
    exact ⟨room R j funded _,room R j funded _⟩
  · intro j bj jf i;exact paid j bj jf i.2

end YM.Integration.WilsonThermometerCorridorLawn
end
