import YM.Next.RANK.Gaussian

/-! Restores the signed Gaussian polynomial inverse identity from the
hash-pinned ancestral source. The existing milk and Symmetric definitions
are reused unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat
open YM.Next.Rank.Normal
variable {V : Type*} (Q : Symmetric V)
lemma thaw (p : poly V) : milk (-Q) (milk Q p) = p := by
  have hc : (-Q) + Q = 0 := Symmetric.ext (neg_add_cancel _)
  rw [warms, hc, froze]
end YM.XSpace.Compat
end
