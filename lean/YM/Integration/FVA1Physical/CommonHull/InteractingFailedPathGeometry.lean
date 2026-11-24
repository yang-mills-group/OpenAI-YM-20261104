import YM.Integration.FVA1Physical.CommonHull.InteractingFailedPathCount
import YM.Push.ABSOLUTE_SUMS.Animals
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Convert any actual support chain to a repeat-free list of true failed
sites. Only the actors reached inside a finite ball about the first marker
have to be short. All remote actors and additional failures are allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Lattice Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {n:Side}

private def flagGraph (F:Support n)(r:ℕ):SimpleGraph (↥F) where
  Adj a b:=a≠b∧separation a.1 b.1≤r
  symm:=⟨fun a b h=>⟨h.1.symm,(separation_comm a.1 b.1) ▸ h.2⟩⟩
  loopless:=⟨fun _ h=>h.1 rfl⟩

private theorem extent {F:Support n}{r:ℕ}{a b:↥F}(p:(flagGraph F r).Walk a b):
    separation a.1 b.1≤r*p.length:=by
  induction p with
  | nil=>simp
  | @cons a z b edge path ih=>
    exact (separation_triangle _ z.1 _).trans ((Nat.add_le_add edge.2 ih).trans_eq
      (by rw [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]))

private theorem list_book {F:Support n}{r:ℕ}{a b:↥F}(p:(flagGraph F r).Walk a b)(x:Site n)
    (near:separation x a.1≤r):p.support.map Subtype.val∈pathBook (neighbors r) x (p.length+1):=by
  induction p generalizing x with
  | nil=>
    exact mem_biUnion.mpr ⟨_,(neighbors_mem _ _ _).2 near,mem_image.mpr ⟨[],mem_singleton_self _,rfl⟩⟩
  | @cons a z b edge path ih=>
    exact mem_biUnion.mpr ⟨_,(neighbors_mem _ _ _).2 near,mem_image.mpr ⟨_,ih _ edge.2,rfl⟩⟩

private def Tether (F:Support n)(w:ℕ)(x y:Site n):Prop:=x=y ∨
  ∃a b:↥F,separation x a.1≤w ∧ (flagGraph F (2*w)).Reachable a b ∧ separation b.1 y≤w

private theorem advance {F:Support n}{w:ℕ}{x u y:Site n}(prior:Tether F w x u)
    (step:∃z∈F,separation u z≤w∧separation z y≤w):Tether F w x y:=by
  obtain ⟨z,hz,uz,zy⟩:=step;let v:↥F:=⟨z,hz⟩
  rcases prior with eq|⟨a,b,birth,conn,tail⟩
  · exact Or.inr ⟨v,v,eq ▸ uz,SimpleGraph.Reachable.refl _,zy⟩
  have edge:(flagGraph F (2*w)).Reachable b v:=by
    by_cases same:b=v
    · rw [same]
    have cost:separation b.1 v.1≤2*w:=(separation_triangle _ u _).trans (by dsimp only [v];omega)
    exact SimpleGraph.Adj.reachable (show (flagGraph F (2*w)).Adj b v from ⟨same,cost⟩)
  exact Or.inr ⟨a,v,birth,conn.trans edge,zy⟩

/-- Separation dichotomy, on the given torus and the given field. A long
actor anywhere else need not be excluded. The endpoint returns at least k
distinct failures linked by short jumps, starting close to the first marker. -/
theorem separation_path {link:Site n→Site n→Prop}(F:Support n)(w k:ℕ)(x y:Site n)
    (chain:Relation.ReflTransGen link x y)(far:2*w*k<separation x y)
    (paid:∀u v,link u v→separation x u≤2*w*k→∃z∈F,separation u z≤w∧separation z v≤w):
    ∃P∈pathBook (neighbors (2*w)) x k,P.Nodup ∧ P.toFinset⊆F:=by
  by_contra! absent
  have bounded(u:Site n)(past:Tether F w x u):separation x u≤2*w*k:=by
    rcases past with eq|⟨a,b,started,reach,ended⟩
    · rw [eq,separation_self];exact Nat.zero_le _
    obtain ⟨p,np⟩:=reach.exists_isPath
    have len:p.length+1<k:=by
      by_contra! threshold
      let L:=p.support.map Subtype.val
      have booked:L∈pathBook (neighbors (2*w)) x (p.length+1):=list_book p x (by omega)
      have distinct:L.Nodup:=List.Nodup.map Subtype.val_injective np.support_nodup
      have step:=path_book_take _ _ _ k booked threshold
      have all:L.toFinset⊆F:=by
        intro z hz;obtain ⟨v,_,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz);exact v.2
      have all':(L.take k).toFinset⊆F:=by
        intro z hz;exact all (List.mem_toFinset.mpr (List.take_subset k L (List.mem_toFinset.mp hz)))
      exact absent _ step ((List.take_sublist k L).nodup distinct) all'
    have dist:=extent p
    have small:2*w*(p.length+1)≤2*w*k:=Nat.mul_le_mul_left _ len.le
    have start:=separation_triangle x a.1 u
    have finish:=separation_triangle a.1 b.1 u
    rw [Nat.mul_succ] at small
    omega
  have follow {v:Site n}(h:Relation.ReflTransGen link x v):Tether F w x v:=by
    induction h with
    | refl=>exact Or.inl rfl
    | tail prior next ih=>exact advance ih (paid _ _ next (bounded _ ih))
  exact (not_le_of_gt far) (bounded _ (follow chain))

end YM.Integration.FVA1Physical.Marked.RemoteRoster
