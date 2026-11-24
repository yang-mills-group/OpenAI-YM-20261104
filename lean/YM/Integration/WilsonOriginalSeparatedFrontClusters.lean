import YM.Integration.WilsonOriginalFlatHull
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Bounded connected components of the overlap graph of the actual marked fronts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedFrontClusters
open Lattice
open scoped Classical
variable {n:Side} {V:Type} [Fintype V]

def cluster (o:V→Site n)(a:ℕ):SimpleGraph V where
  Adj v w := v≠w ∧ separation (o v) (o w) ≤ a
  symm := ⟨fun v w h=>⟨Ne.symm h.1,by simpa only [separation_comm (o w) (o v)] using h.2⟩⟩
  loopless := ⟨fun _ h=>h.1 rfl⟩

omit [Fintype V] in
private theorem distance (o:V→Site n)(a:ℕ){v w:V}(p:(cluster o a).Walk v w):
    separation (o v) (o w) ≤ p.length*a := by
  induction p with
  | nil=>simp
  | @cons u v w edge p ih=>
    have link:separation (o u) (o v) ≤ a := edge.2
    exact (separation_triangle (o u) (o v) (o w)).trans
      (by simpa only [SimpleGraph.Walk.length_cons,Nat.add_mul,one_mul,Nat.add_comm (p.length*a) a]
        using Nat.add_le_add link ih)

def front (o:V→Site n)(a:ℕ)(v:V):V := Quot.out ((cluster o a).connectedComponentMk v)

theorem extent (o:V→Site n)(a:ℕ)(v:V):
    separation (o (front o a v)) (o v) ≤ (Fintype.card V-1)*a := by
  have same:(cluster o a).connectedComponentMk (front o a v)=(cluster o a).connectedComponentMk v := Quot.out_eq _
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact same
  let q := p.toPath
  exact (distance o a q.val).trans (Nat.mul_le_mul_right a (by have h := q.property.length_lt;omega))

omit [Fintype V] in
theorem overlapping (o:V→Site n)(k:ℕ){v w:V}{x:Site n}
    (hx:separation (o v) x ≤ k)(hy:separation (o w) x ≤ k):
    front o (2*k+2) v=front o (2*k+2) w := by
  by_cases same:v=w
  · rw [same]
  have dist := separation_triangle (o v) x (o w)
  rw [separation_comm x (o w)] at dist
  have edge:(cluster o (2*k+2)).Adj v w := ⟨same,by omega⟩
  exact congrArg Quot.out (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj edge)

def crop (B count:ℕ):ℕ := B/(64*(count+1))

theorem fits (B count:ℕ)(late:64*(count+1) ≤ B):
    let m := crop B count
    let k := 2*m+2
    2*((count-1)*(2*k+2)+k)<B := by
  let m := crop B count
  let k := 2*m+2
  change 2*((count-1)*(2*k+2)+k)<B
  have pos:0<64*(count+1) := by positivity
  have h:1 ≤ m := (Nat.le_div_iff_mul_le pos).2 (by simpa using late)
  have paid:m*(64*(count+1)) ≤ B := Nat.div_mul_le_self B _
  have larger:(count-1)*(2*k+2)+k ≤ (count+1)*(2*k+2) := by
    rw [Nat.add_mul,one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le count 1)) (by omega)
  calc
    _ ≤ 2*((count+1)*(2*k+2)) := Nat.mul_le_mul_left 2 larger
    _=(count+1)*(2*(2*k+2)) := by ring
    _<(count+1)*(64*m) := Nat.mul_lt_mul_of_pos_left (by dsimp [k];omega) (by omega)
    _=m*(64*(count+1)) := by ring
    _ ≤ B := paid

end YM.Integration.WilsonOriginalSeparatedFrontClusters
end
