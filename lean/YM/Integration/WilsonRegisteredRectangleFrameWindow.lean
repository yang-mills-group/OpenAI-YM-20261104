import YM.Integration.WilsonPhysicalLocalPlaquetteRoutes
import YM.Integration.WilsonRegisteredRectangleTags

/-! The true frame minimizing criterion on a finite physical plaquette collar. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameWindow
open Lattice RG RG.Patch Axial Wilson Pressure Function Finset
open scoped BigOperators Classical
variable {G:Gauge}

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

def charge (P:RG.Patch)(θ:ℝ):ℝ:=
  4*((2*(P.radius:ℝ)+1)*(4*((P.radius+1:ℕ):ℝ)*((Fintype.card PlaqAxes:ℝ)*θ)))

theorem cover (P:RG.Patch)(K:RG.KernelChoices)(U:CoverConfig G)(θ:ℝ)(hp:0≤θ)
    (faces:∀x∈Lattice.box (P.radius+1),∀b:PlaqAxes,G.chord (faceValue U (x,b)) ≤ θ)
    (room:charge P θ<K.frame_cut):P.usesMin K U:=by
  intro l k x y
  let phase:=Axial.traveller (allAxes l) U 0
  let V:=Lattice.gauge phase U
  let b:=4*((P.radius+1:ℕ):ℝ)*((Fintype.card PlaqAxes:ℝ)*θ)
  have bonds (z:Cover) (hz:z∈Lattice.box P.radius) (a:Axis):G.chord (V (z,a))≤b:=by
    have hn:z+step a∈Lattice.box (P.radius+1):=by
      obtain ⟨lo,hi⟩:=box_test.mp hz
      rw [box_test];constructor <;> intro i <;> simp only [Pi.add_apply,step_apply] <;> split <;>
        have hl:=lo i <;> have hh:=hi i <;> omega
    exact Planned.PrimaryIntegral295.Racks.axle l (P.radius+1) θ hp U faces (z,a)
      (Planned.PrimaryIntegral295.Racks.within (Nat.le_succ _) hz) hn
  have bound:=routed P.radius V b (by dsimp [b];positivity) bonds (allAxes k)
    ((List.nodup_finRange _).map k.injective) x y
  have same:P.via (P.axial U (P.center,l)) U x y k=travel V x.val (route x.val y.val k):=by
    change _=travel (Lattice.gauge phase U) x.val (route x.val y.val k)
    rw [travel_gauge,route_end]
    rfl
  rw [same]
  have size:(allAxes k).length=4:=by simp [allAxes]
  rw [size] at bound
  exact lt_of_le_of_lt bound room

theorem placed {c f:Side}(S:StepData c f)(o:Site c)(U:Config G f)(θ:ℝ)(hp:0≤θ)
    (faces:∀x∈WilsonAxialWindow.cells (S.ratio.embed o) (S.patch.radius+1),G.chord (faceValue U x) ≤ θ)
    (room:charge S.patch θ<S.kernel.frame_cut):
    S.patch.usesMin S.kernel (expandAt (S.ratio.embed o) U):=by
  apply cover S.patch S.kernel _ θ hp _ room
  intro x inside a
  rw [WilsonAxialWindow.expanded]
  exact faces _ (WilsonAxialWindow.cell _ _ inside _)

end YM.Integration.WilsonRegisteredRectangleFrameWindow
