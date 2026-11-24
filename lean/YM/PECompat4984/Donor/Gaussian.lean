import YM.Next.RANK.Gaussian
import YM.Maxwell.Wick
import Mathlib.Algebra.MvPolynomial.Derivation

/-! Exact seed helper restoration; retained definitions are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Finsupp Function Set
open scoped BigOperators

variable {V Z : Type*}

namespace Symmetric

lemma cancels' (p : Symmetric V) : (-p)+p=0 := ext (neg_add_cancel _)

end Symmetric

variable (Q : Symmetric V) (i : V)

lemma thaw (p : poly V) : milk (-Q) (milk Q p)=p := (warms ..).trans ((Q.cancels' ▸ (show milk (0:Symmetric V) p = p from froze p)))

end YM.Next.Rank.Normal
end
