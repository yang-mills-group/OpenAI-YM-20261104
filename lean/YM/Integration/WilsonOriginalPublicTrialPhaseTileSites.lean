import YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice

/-! The true centered reflected copies retain the same per-site load on both
sides of an original Wilson step. All occupied locations and all windings are kept. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTileSites
open Finset Function Lattice Wilson RG Cells Push Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon Extra.Multi
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G){j m p:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "B" => (C).S.oneStep m p

theorem parent (jm : j ≤ m) (i:(tilesAt (C).S p jm).Cell)(z:Site ((C).side (m+1) p)):
    (B).parent ((tilesAt (C).S p (jm.trans m.le_succ)).copyMap i z) =
    (tilesAt (C).S p jm).copyMap i ((B).parent z):=by
  rw [Tiling.copyMap,Tiling.copyMap,tile_translate,tile_translate,←anchor_next (C).S p jm i,
    Local.parent_affine (B) ((C).S.block_odd m)]
  rfl

private theorem located {n k:Side}{V:Type}[Fintype V](π:Site n→Site k)(o:V→Site n)(y:V→Site k)
    (A:ℕ)(same:∀v,π (o v)=y v)(paid:Occupancy y A):Occupancy (π ∘ o) A:=by
  have e:π ∘ o=y:=funext same
  rw [e]
  exact paid

set_option maxHeartbeats 500000 in
theorem original (jm : j ≤ m)(z:I→Site ((C).side (m+1) p)):
    let T:=tilesAt (C).S p (jm.trans m.le_succ)
    let o:=fun i:T.Cell×I=>T.copyMap i.1 (z i.2)
    let cap:=Fintype.card I*Fintype.card Signed
    Occupancy o cap ∧ Occupancy ((B).parent ∘ o) cap:=by
  intro T o cap
  let U:=tilesAt (C).S p jm
  let y:T.Cell×I→Site ((C).side m p):=fun v=>U.copyMap v.1 ((B).parent (z v.2))
  refine ⟨WilsonOriginalPublicTrialPhaseTiles.seats T z,
    located (B).parent o y cap (fun i=>parent R jm i.1 (z i.2)) ?_⟩
  exact WilsonOriginalPublicTrialPhaseTiles.seats U (fun i:I=>(B).parent (z i))

end YM.Integration.WilsonOriginalPublicTrialPhaseTileSites
end
