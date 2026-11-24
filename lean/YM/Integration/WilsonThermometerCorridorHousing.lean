import YM.Integration.WilsonThermometerRegisteredCapturedPaths
import YM.Integration.WilsonThermometerRegisteredTripleRoom
import YM.Integration.WilsonThermometerCorridorLawn
/- The two true taps of the complete named separated incoming R gallery at
   its exact reference f use the affordable rides from the earlier grouped
   date. The continuation below f has the same actors on every original mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorHousing
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

open QuadraticLocal
open Extraction Cells XSpace WilsonThermometerAlignedCells
theorem original (simple:G.Simple)(φ:Test 3):
    ∀ᶠ b:ℕ in atTop,∀N p (_:b≤N)(r:ℝ),|r|≤(CF).S.a b → ∀y:Site ((CF).side N p)×Site ((CF).side N p),
      mass (R:=R) r (N,p) φ y≠0 →
      let o:=origins R (atOrigin y) b
      let P:=(CF).path.rep N p b
      o 0=0 ∧ ∀i:Fin 3,coverNumber P.p.B ({o 0,o i}:Support ((CF).side b p))≤81:=by
  filter_upwards [WilsonThermometerRegisteredTripleRoom.spatial R simple φ] with b bought N p live r radius y paid
  dsimp only
  have identity (v:Fin 3):origins R (atOrigin y) b v=((CF).S.toDepth live p).parent (atOrigin y v):=by
    unfold origins WilsonThermometerOwnOffsetNectar.location;rw [dif_pos live];rfl
  have params:((CF).path.rep N p b).p=(A).budget b:=(R.makes.wilson.represents N p b live).vac
  have covers (v:Fin 3):origins R (atOrigin y) b v ∈ halo (((CF).path.rep N p b).p.B) {0}:=by
    rw [params,identity]
    exact halo_spec.mpr ⟨0,mem_singleton_self _,(separation_comm 0 _).le.trans (bought N p live r radius y paid v)⟩
  constructor
  · rw [identity];exact WilsonThermometerRegisteredPairRoom.zero _
  · intro i
    have sub:({origins R (atOrigin y) b 0,origins R (atOrigin y) b i}:Support _) ⊆ halo (((CF).path.rep N p b).p.B) {0}:=by
      intro x hx
      rcases mem_insert.mp hx with z|z
      · exact z ▸ covers 0
      · exact (mem_singleton.mp z) ▸ covers i
    refine (Corona.cover_mono sub _).trans ?_
    simpa using (Corona.tile (0:Site ((CF).side b p)) 1 ((CF).path.rep N p b).p.B ((CF).path.rep N p b).p.B_pos)
end YM.Integration.WilsonThermometerCorridorHousing
end
