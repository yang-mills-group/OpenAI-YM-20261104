import Mathlib.Data.List.Basic

/-!
# Explicit rooted growth order for finite tensor contractions

The edge label is retained at every step.  A new vertex is joined by the
recorded directed edge from the previously visited vertices.  Coverage is a
separate hypothesis; the declaration does not assert any contraction bound.
-/

set_option autoImplicit false

namespace YM.Integration.AnchoredTensorContraction

inductive Growth {V J : Type*} (src dst : J → V) (root : V) : List J → Prop where
  | nil : Growth src dst root []
  | snoc {es : List J} (previous : Growth src dst root es) (e : J)
      (hsrc : src e ∈ root :: es.map dst)
      (hdst : dst e ∉ root :: es.map dst) :
      Growth src dst root (es ++ [e])

end YM.Integration.AnchoredTensorContraction
