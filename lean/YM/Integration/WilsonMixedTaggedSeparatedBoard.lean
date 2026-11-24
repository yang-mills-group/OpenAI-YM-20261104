import YM.RG05Readout.Many.Pick

/-! The separated ancestor census of the true addressed source at every ultraviolet
date.  Each coefficient comes from the full signed Wilson replay by restriction.
The same bound certifies its regular terms and its charged hard terms. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedSeparatedBoard
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d k:ℕ} {W:Type} [DecidableEq W] [Fintype W]
    {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ)
variable (I:∀ i:ℕ, ManyStem C o i→Body)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "origins" => (A).supportX
variable (h:C.Makes) (L:OPE.Package C w r D) (stock:Storage C D)
variable (P:(j:W)→Sight C (s j) p) (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j))
variable {B:ℕ→ℕ→ℝ} {Q:ℝ} (roster:Census W)
local notation "Y" => C.path.rep N p
local notation "rows" => plants (m:=m) s P S x
local notation "vec" => Launch (m:=m) s S x
local notation "born" => fun i:ManyStem C o N=>stepUp ((A).motion (Λ N i)) (origins N i)
      (entrance C (s (Λ N i)) N p (vec (Λ N i) N) 0 (I N i))

theorem admitted {i:ℕ} (nm:n ≤ m) (mi:m ≤ i) :
    (Mine.masts o E nm (barren o E roster m) i).choices ⊆ (Mine.ward o E roster i).choices :=
  Mine.masts_le o E nm _ _ (Finset.filter_subset ..) mi

variable {F:∀i:ℕ,Config G (C.side i p)→Poly (Mine.ward o E roster i)}
include h L stock in
theorem original (basis:∀j:W,Spine D B h n p (s j) N (P j) (S j))
    (nm:n ≤ m) (mN:m ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (prepared:PreparedA A I n N le_rfl) (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (I n j) 1)
    (sizeBound:∀j:W,size (x j) ≤ Q) (positive:0<Q) (warm:Warm C n (d+1) k) (degrees:∀j:W,s j ≤ d)
    (top:F N=birth (Mine.ward o E roster N) (Y N) born) (replay:Replay A s (H:=Mine.ward o E roster) le_rfl N F N) :
    ∀i, ∀mi:m ≤ i,∀iN:i ≤ N,
      MenuBoard (Y i) (imprint h A I rows i iN)
        (fun U=>narrow (admitted o E roster nm mi) (F i U)) (origins i)
        (fun _=>envelope C m (d+1) k Q i)
        (if i=N then (C.path.levels.budget i).supportExponent-4 else (C.path.levels.budget i).supportExponent) 1 := by
  let amount:=Many.total C Q (d+1) m
  let area:=rusty C m k
  have purse:= ignite (Q:=Q) (m:=m) (N:=N) warm positive (d:=d+1) (by omega)
  have lesson:Lesson (D:=D) h s n N N p rows B amount vec:=by
    refine ⟨fun j => ⟨P j,S j,basis j,fun _=>rfl,fun i _ _=>nearpoints (S j) (x j) _,fun i ni iN=>?_⟩⟩
    exact head_cost (basis j) nm mN (Nat.add_le_add_right (degrees j) _) (sizeBound j) ni iN
  let chosen:=barren o E roster m
  let H:=Mine.masts o E nm chosen
  have choices:Choices o E m chosen:=barraged o E roster
  have occupy (i:ℕ) (ni:n ≤ i) := Mine.pays o E ni occupied le_rfl
  have course:Toured A H nm N area k:=by
    refine ⟨fun i mi _=>(occupy i (nm.trans mi)).1,fun i mi _=>(occupy i (nm.trans mi)).2,fun i mi iN=>?_⟩
    apply Cushions.via (Mine.shelter_test o E nm mi chosen L.tabs choices)
    change rusty C m k i ≤ rusty C m k (i+1)
    rw [rust_above mi,rust_above (mi.trans i.le_succ)]
  have crowded:Occupancy (origins N) (apron C.path.levels N):=by
    intro z
    apply le_trans (keep_occ o E (nm.trans mN) occupied z)
    have hJ: C.path.levels.clock.J n ≤ C.path.levels.clock.J (N+1)+2:=
      (C.path.levels.fits.mono ((nm.trans mN).trans N.le_succ)).trans (Nat.le_add_right _ _)
    exact hJ.trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block N).property _))
  obtain ⟨filtered,hreplay,origin⟩:=reels_write A s nm mN (H:=H) (fun i mi iN=>Mine.dawnwide o E nm chosen mi)
    (birth (H N) (Y N) born) N
  have capM:=cap_lives A s I le_rfl nm mN prepared cap
  have prepM:PreparedA A I m N nm:=fun i mi iN=>prepared i (nm.trans mi) iN
  have board:=assemble A s I h L stock nm mN (purse.slice nm le_rfl) (lesson.revise s h nm le_rfl)
    (fun j jd=>(warm.lanes _ jd).trans (nm.trans mN)) (fun j=>(degrees j).trans d.le_succ)
    capM prepM origin (fun j jd=>warm.buys j _ jd (nm.trans mN)) crowded course hreplay
  have liveTop:Integrable (F N) (prior G _):=by rw [top];exact seen_top A s I h
  intro i mi iN
  have same:filtered i = fun U=>narrow (admitted o E roster nm mi) (F i U):=by
    funext U
    apply hreplay.narrowing A s nm le_rfl nm replay (fun j mj=>admitted o E roster nm mj) mN liveTop le_rfl _ mi iN U
    intro V
    rw [top,origin]
    exact (birth_choice _ _ (admitted o E roster nm mN) V).symm
  rw [←same]
  exact board i mi iN

end YM.Integration.WilsonMixedTaggedSeparatedBoard
