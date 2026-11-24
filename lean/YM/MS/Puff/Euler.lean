import YM.MS.Puff.Ring

set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset Real
open Book Book.Convolve
open scoped Topology
variable {I E: Type} [AddCommGroup E] [Module ℂ E]
variable {M:Actors E}
variable (P:SplitP I)
namespace Actors
variable (M) (B:E)
local infix:70 " ⋆ " => M.core
def power : ℕ→E | 0=> M.unit| k+1=> B ⋆ power k
abbrev phase (k:ℕ): ℂ:= ((k.factorial:ℕ):ℂ)⁻¹
def wages (M:Actors E)(F:E)(n:ℕ) : E:= phase n • M.power F n
def cheers (M:Actors E)(F:E)(n:ℕ): E:= ∑ i∈ Finset.range (n+1),M.wages F i
section eval
local notation "gP"=> M.stack P
variable (b:I→E)
def Cheer : I→E:= fun i=> (gP).cheers b (P.grade i) i
end eval
end Actors
end YM.MS.Puff
