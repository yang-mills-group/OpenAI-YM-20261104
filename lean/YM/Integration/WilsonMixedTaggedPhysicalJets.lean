import YM.RG05Readout.Pulse.Chills

/-! One original nuclear bouquet reconstructs the physical test on the union
of the actual residue grids of every date, at the original RG05 price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedPhysicalJets
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {W:Type} [DecidableEq W] [Fintype W] {b N per d:ℕ}

def Exact (s:W→ℕ) (Ψ:Wave W) (o:W→Site (C.side b per)) (r:ℝ) (N:ℕ) (F:E4→Wave W) : Prop :=
  ∀j:ℕ,∀bj:b ≤ j,j ≤ N → ∀(τ:E4)(k:ℕ),k ≤ ∑v,s v →
    ∀w:W→Site (C.S.toDepth bj per).count,pie (F τ) (cropX Ψ o r τ) k (placeR (C.S.toDepth bj per) ∘ w)

theorem original (s:W→ℕ) (o:W→Site (C.side b per)) (r η:ℝ) (Ψ:Wave W)
    (rp:0 < r) (below:r ≤ C.S.a b) (ep:0 < η) (small:η ≤ 1)
    (order:(∑v:W,(s v+2))+4*Fintype.card W < d+1) (far:Scattering Ψ η)
    {X:ℝ} (xp:0 ≤ X) (price:Tall Ψ (d+1) 1 X) :
    ∃F:E4→Wave W,Bouquet s Native.box (buy C b per o (r*η/2)) F (earn s C b d η r*X) ∧
      Exact s Ψ o r N F := by
  let D:Type:={j:Fin (N+1)//b ≤ j.val}
  let A (j:D):=C.S.toDepth j.property per
  let grid (j:D):Finset (Cloud W):=Finset.univ.image
    (fun w:W→Site (A j).count=>placeR (A j) ∘ w)
  let L:=Finset.univ.biUnion grid
  let z:=gustCost C b η r
  have zp:0 < z:=div_pos (mul_pos (by positivity) rp) (C.S.a_pos _)
  have z1:z ≤ 1:=by
    unfold z gustCost
    rw [div_le_one (C.S.a_pos _)]
    exact (mul_le_of_le_one_left rp.le (by linarith)).trans below
  have spread:r*η/2+2*C.S.a b*(2*z) ≤ r*η:=by
    unfold z gustCost
    have a:=C.S.a_pos b
    field_simp
    norm_num
    try linarith
  have lives (v:Cloud W) (present:v∈L):‖v‖ < (2:ℝ) := by
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp present
    obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hj
    apply lt_of_le_of_lt _ one_lt_two
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
    intro i
    apply Pert.Cellular.cells_bd
    change placeR (A j) (w i)∈Native.box
    simpa only [smul_zero,add_zero] using mapsR (A j) (C.S.toDepth_odd _ _) (w i) Native.box0
  obtain ⟨F,funded,exactly⟩:=Nuclear.vitality s Native.box (buy C b per o (r*η/2))
    (cropX Ψ o r) 2 z L (crop_cont o r Ψ) (territory o r η Ψ far rp _ _ spread)
    (fun i _=>inflame o r Ψ rp below price i)
    (show 0 ≤ (C.S.a b/r)^(d+1)*X from mul_nonneg (pow_nonneg (div_nonneg (C.S.a_pos _).le rp.le) _) xp)
    le_rfl zp z1 order zero_le_two lives
  refine ⟨F,funded.permit (fun _ _=>rfl) (le_of_eq ?_),?_⟩
  · unfold earn z
    dsimp only
    ring
  intro j bj jN τ k degree w
  let i:D:=⟨⟨j,by omega⟩,bj⟩
  have address:placeR (C.S.toDepth bj per) ∘ w ∈ L :=
    Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩⟩
  apply exactly τ _ address k
  have h:=degree.trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun v:W=>s v+2)
    (fun v _=>Nat.le_add_right ..))
  omega

end YM.Integration.WilsonMixedTaggedPhysicalJets
