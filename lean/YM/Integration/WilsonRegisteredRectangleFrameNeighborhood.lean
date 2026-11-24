import YM.Integration.WilsonRegisteredRectangleFrameData
import YM.RG03.BoardHull
import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Lattice.Crossing

/-! All native link tails read in the true site and bond tags lie in a specified finite torus ball. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameNeighborhood
open Lattice Wilson RG Finset WilsonRegisteredRectangleFrameData
open scoped Classical
variable {G:Gauge}{n:Side}

def room (P:Patch):ℕ:=10*(P.radius+P.L.val+1)

def agrees (o:Site n)(r:ℕ)(U V:Config G n):Prop:=∀e:Edge (Site n),separation o e.1≤r → U e=V e

private theorem bounded_travel {o x:Site n}{U V:Config G n}{r:ℕ}(w:Walk)
    (agree:agrees o r U V)(span:separation o x+w.length≤r):travel U x w=travel V x w:=by
  apply travel_local x w U V
  intro e inside _
  exact agree e ((separation_triangle o x e.1).trans ((Nat.add_le_add_left (RG03.Tight.on_walk x w e.1 inside) _).trans span))

private theorem route_budget (P:Patch)(x y:P.Points)(k:Lattice.Order):(route x.val y.val k).length≤8*P.radius:=by
  rw [Extra.Iteration.route_length]
  change (∑j:Axis,(y.val j-x.val j).natAbs)≤_
  calc
    _ ≤ ∑_j:Axis,2*P.radius:=sum_le_sum fun j _=>by
      have xlo:=(box_test.mp x.property).1 j;have xhi:=(box_test.mp x.property).2 j
      have ylo:=(box_test.mp y.property).1 j;have yhi:=(box_test.mp y.property).2 j
      omega
    _ = _:=by simp [Axis];omega

theorem site (P:Patch)(o:Site n){U V:Config G n}(agree:agrees o (room P) U V):
    Chart P (expandAt o U) (expandAt o V):=by
  constructor
  · intro x y k;rw [travel_at,travel_at];apply bounded_travel _ agree
    have bound:=route_budget P x y k
    have initial:=Work.E08.separation_box_add o x.property
    unfold room;omega
  · intro x j;apply agree;exact (Work.E08.separation_box_add o x.property).trans (by unfold room;omega)
  · intro x a;unfold faceValue;rw [travel_at,travel_at];apply bounded_travel _ agree
    have initial:=Work.E08.separation_box_add o x.property
    simp only [square,List.length_cons,List.length_nil];unfold room;omega

variable {c f:Side}(S:StepData c f)
def bondRoom:ℕ:=S.patch.L.val+room S.patch

theorem jump (x:Site c)(k:Axis):separation (S.ratio.embed x) (S.ratio.embed (x+step k))≤S.patch.L.val:=by
  let z:Cover:=S.patch.L.val • (step k:Cover)
  have hz:z∈box S.patch.L.val:=by
    rw [box_test];constructor
    · intro j;change -(S.patch.L.val:ℤ)≤S.patch.L.val • (step k:Cover) j
      rw [step_apply];split <;> simp
    · intro j;change S.patch.L.val • (step k:Cover) j≤(S.patch.L.val:ℤ)
      rw [step_apply];split <;> simp
  have hs:=Work.E08.separation_box_add (S.ratio.embed x) hz
  rw [S.ratio.embed_leap]
  simpa only [z,map_nsmul,wrap_step,add_comm,StepData.ratio] using hs

theorem all_bond (e:Edge (Site c)){U V:Config G f}(agree:agrees (S.ratio.embed e.1) (bondRoom S) U V):
    BondData S U V e:=by
  constructor
  · apply site;intro i hi;apply agree;dsimp [bondRoom];omega
  · apply site;intro i hi;apply agree
    exact (separation_triangle _ _ _).trans (Nat.add_le_add (jump S e.1 e.2) hi)
  · intro x;rw [travel_at,travel_at];apply bounded_travel _ agree
    have hl:=Work.E08.separation_box_add (S.ratio.embed e.1) x.property
    simp only [List.length_replicate];unfold bondRoom room;omega

end YM.Integration.WilsonRegisteredRectangleFrameNeighborhood
