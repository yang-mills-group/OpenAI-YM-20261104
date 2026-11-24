import YM.MS.Puff.Ring
import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Pairs

/-!
Bilinear algebra for lift of identities through both perturbative order and marker index.
Mark message always in original finite-set indices. The spectrum of engineering dimensions does not matter.
We intentionally restrict all assertions within the even part (including the primitive/wave-adjusted
insertions of ghost number zero). Evenness, time evolution and parity will be supplied explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve
open scoped Topology ContDiff Interval
variable {E F H A I J Z W:Type}
  [AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F] [AddCommGroup H][Module ℂ H]


variable (P:SplitP I)
namespace SplitP

end SplitP

-- Guard-based commutative algebra
namespace Actors
variable (M:Actors E)
local infix:70 " ⋆ " => M.core

end Actors
end YM.MS.Puff
