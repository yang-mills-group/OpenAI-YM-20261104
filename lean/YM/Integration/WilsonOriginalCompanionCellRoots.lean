import YM.Integration.WilsonThermometerCorridorHousing
import YM.Integration.WilsonOriginalCompanionPeerRefund

/-! Real shifted thermometer cells give all canonical roots and the shared terminal halo before either cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionCellRoots
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "CF"=>R.family
local notation "A"=>(CF).path.levels
local notation "X"=>Unit×(Fin 3×Bool)
open Extraction Cells XSpace WilsonThermometerAlignedCells WilsonThermometerOwnOffsetJoint
def center:(X):=((),(0,false))
def route {N p:ℕ}(y:Site ((CF).side N p)×Site ((CF).side N p))(k:ℕ)(i:(X)):Site ((CF).side k p):=
  origins R (atOrigin y) k i.2.1
theorem original (simple:G.Simple)(φ:Test 3):
    ∀ᶠ j:ℕ in atTop,∀N p f (_:j+2≤f) (_:f≤N)(r:ℝ),|r|≤(CF).S.a (j+1) →
    ∀y:Site ((CF).side N p)×Site ((CF).side N p),mass (R:=R) r (N,p) φ y≠0 →
      route R y f=(origins R (atOrigin y) f ∘ Prod.fst) ∘ Prod.snd ∧
      (∀k:ℕ,j+1≤k → k<f → route R y k=((A).clock.op k p).ratio.parent ∘ route R y (k+1)) ∧
      (∀i,coverNumber ((CF).path.rep N p (j+1)).p.B ({route R y (j+1) center,route R y (j+1) i}:Support _)≤81) ∧
      ((A).clock.op j p).ratio.parent (route R y (j+1) center)=0:=by
  obtain ⟨age,all⟩:=eventually_atTop.mp (WilsonThermometerCorridorHousing.original R simple φ)
  filter_upwards [eventually_ge_atTop age] with j late N p f height fn r span y paid
  obtain ⟨zero,room⟩:=all (j+1) (by omega) N p (by omega) r span y paid
  refine ⟨rfl,?_,fun i=>room i.2.1,?_⟩
  · intro k _ kf
    funext i
    exact (WilsonThermometerOwnOffsetGeometry.parent R (atOrigin y) (show k<N by omega) i.2.1).symm
  · change ((A).clock.op j p).ratio.parent (origins R (atOrigin y) (j+1) 0)=0
    rw [zero,WilsonThermometerRegisteredPairRoom.zero]

end YM.Integration.WilsonOriginalCompanionCellRoots
end
