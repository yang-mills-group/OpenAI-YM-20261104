import YM.MS.Local.Differential

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Tensor MatrixLet
open Landau Detect Detect.Mark Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {h: ℤ} {f: Grade G}
abbrev Horizontal (f:Grade G)(h:ℤ):= f∈ yields h 0 ∧ Q f=0
lemma Tall_l (H : Horizontal f h) (i : Lane4 G) (he:f i≠0): ∃ a k p,i=W a k p:= by
   have ht := (seedStar.mp H.1).real' i; rcases i with ⟨⟨⟨_|i,_|_⟩,k⟩,p⟩ <;> first | (refine absurd (ht ?_) he; norm_num [ghostNo,ghostChannel]; done)| exact ⟨i,k,p,rfl⟩
end YM.MS.Local.BV
