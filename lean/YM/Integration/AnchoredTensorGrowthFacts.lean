import YM.Integration.AnchoredTensorContraction
import Mathlib.Data.List.Nodup

/-!
# Uniqueness and endpoint membership for a rooted growth order

These are consequences of the recorded old-to-new growth steps. They add
no connectedness, tree, endpoint, or cardinality hypothesis.
-/

set_option autoImplicit false

namespace YM.Integration.AnchoredTensorContraction

variable {V J : Type*} {src dst : J → V} {root : V} {es : List J}

theorem Growth.vertices_nodup (g : Growth src dst root es) :
    (root :: es.map dst).Nodup := by
  induction g with
  | nil => simp
  | @snoc es _previous e _hsrc hdst ih =>
    rw [List.map_append, List.map_singleton]
    change ((root :: es.map dst) ++ [dst e]).Nodup
    rw [List.nodup_append_comm]
    exact List.nodup_cons.mpr ⟨hdst, ih⟩

theorem Growth.edges_nodup (g : Growth src dst root es) :
    es.Nodup :=
  List.Nodup.of_map dst (List.nodup_cons.mp g.vertices_nodup).2

private theorem member_append (tail : List J) {v : V}
    (hv : v ∈ root :: es.map dst) :
    v ∈ root :: (es ++ tail).map dst := by
  rcases List.mem_cons.mp hv with hroot | hrest
  · exact List.mem_cons.mpr (Or.inl hroot)
  · apply List.mem_cons.mpr
    right
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hrest)

theorem Growth.source_mem (g : Growth src dst root es) (e : J)
    (he : e ∈ es) : src e ∈ root :: es.map dst := by
  induction g generalizing e with
  | nil => simp at he
  | @snoc es _previous j hsrc _hdst ih =>
    rcases List.mem_append.mp he with hprev | hlast
    · exact member_append [j] (ih e hprev)
    · have heq : e = j := by simpa only [List.mem_singleton] using hlast
      subst e
      exact member_append [j] hsrc

end YM.Integration.AnchoredTensorContraction
