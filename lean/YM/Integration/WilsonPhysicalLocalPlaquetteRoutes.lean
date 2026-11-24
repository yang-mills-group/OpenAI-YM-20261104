import YM.Integration.WilsonPhysicalLocalPlaquetteLoop
import YM.Pressure.Route
import YM.Integration.WilsonAxialWindow

/-! A single actual torus route is paid only on the coordinate rectangle
between its endpoints, even for a support crossing a periodic seam. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalLocalPlaquetteRoutes
open Lattice RG RG.Patch Axial Wilson Pressure Function Finset
open scoped BigOperators Classical
variable {G:Gauge} {n:Side}

private theorem routed (D:ℕ) (V:CoverConfig G) (K:ℝ) (pos:0≤K)
    (bonds:∀x∈Lattice.box D,∀j:Axis,G.chord (V (x,j))≤K)
    (p:List Axis) (uniq:p.Nodup) (x y:Place D):
    G.chord (travel V x.val (axisRoute x.val y.val p))≤p.length*((2*(D:ℝ)+1)*K):=by
  induction p using List.reverseRecOn with
  | nil=>simp [axisRoute,travel]
  | append_singleton p j ih=>
    rw [List.nodup_append] at uniq
    have hj:j∉p:=fun h=>uniq.2.2 j h j (by simp) rfl
    let u:=discord D p x y
    have he:stop x.val (axisRoute x.val y.val p)=u.val:=by
      rw [axisRoute_end x.val y.val x.val p uniq.1];funext i;simp only [u,discord];split <;> simp_all
    have hu:u.val j=x.val j:=if_neg hj
    have walk:=step_cost D j V u (⟨y.val j,(box_iff_layers ..).mp y.property j⟩:Height D)
    rw [hu] at walk
    have localBound (t:Height D):perEdge (Lattice.box D) V (slide D j u t).val j≤K:=by
      unfold perEdge;split
      · exact bonds _ (slide D j u t).property j
      · exact pos
    have budget:(∑ t:Height D,perEdge (Lattice.box D) V (slide D j u t).val j)≤(2*(D:ℝ)+1)*K:=by
      calc
        _≤∑ _t:Height D,K:=Finset.sum_le_sum (fun i _=>localBound i)
        _=_:=by simp [Height,card_layers]
    rw [axisRoute_append,travel_append,he]
    simp only [axisRoute,List.flatMap_singleton]
    apply (G.chord_triangle _ _).trans
    apply (add_le_add (ih uniq.1) (walk.trans budget)).trans_eq
    simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one];ring

theorem centered (o x:Site n) (D:ℕ) (hx:separation o x≤D) (V:Config G n) (K:ℝ) (pos:0≤K)
    (bonds:∀e:Edge (Site n),separation o e.1≤D→G.chord (V e)≤K):
    G.chord (travel V x ((WilsonPhysicalAnchoredPaths.roads o).arm x))≤4*((2*(D:ℝ)+1)*K):=by
  let l:=lift (o-x)
  have hl:l∈Lattice.box D:=Work.E08.lift_mem_box (by rwa [separation_comm] at hx)
  have hneg:-l∈Lattice.box D:=by
    obtain ⟨lo,hi⟩:=box_test.mp hl;rw [box_test];constructor <;> intro i <;>
      simp only [Pi.neg_apply] <;> have a:=lo i <;> have b:=hi i <;> omega
  have shift: (WilsonPhysicalAnchoredPaths.roads o).arm x=route (-l) 0 1:=by
    unfold WilsonPhysicalAnchoredPaths.roads route axisRoute
    apply List.flatMap_congr;intro i _
    congr 1
    change lift x i + l i - lift x i = 0 - -l i
    abel
  have origin:wrap n (-l)+o=x:=by simp [l]
  have cap (z:Cover) (hz:z∈Lattice.box D) (i:Axis):G.chord ((expandAt o V) (z,i))≤K:=
    bonds (wrap n z+o,i) (Work.E08.separation_box_add o hz)
  obtain hs:=routed D (expandAt o V) K pos cap (allAxes 1)
    ((List.nodup_finRange _).map (1:Order).injective) ⟨-l,hneg⟩ ⟨0,center_box D⟩
  change G.chord (travel (expandAt o V) (-l) (route (-l) 0 1))≤_ at hs
  rw [travel_at,origin] at hs
  rw [shift];simpa [allAxes] using hs

end YM.Integration.WilsonPhysicalLocalPlaquetteRoutes
