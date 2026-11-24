import YM.Next.RANK.GaussTags

/-! Restored polynomial evaluation/posting identity from the hash-pinned Oct15
source. New compatibility namespace; no baseline definition is replaced. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat
open MvPolynomial YM.Next.Rank.Normal
variable {A V : Type*}
lemma read_once (i : A) (m : A × V → ℂ) (b : V → ℂ)
    (hb : ∀ z, m (i,z) = b z) (x : poly V) :
    aeval m (post i x) = aeval b x := by
  have hx : (aeval m).comp (post i) = aeval b := by
    ext z
    simp only [AlgHom.comp_apply, post_X, aeval_X]
    exact hb _
  exact DFunLike.congr_fun hx x
end YM.XSpace.Compat
end
