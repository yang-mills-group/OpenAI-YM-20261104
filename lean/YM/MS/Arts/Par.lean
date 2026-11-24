import YM.MS.SineMomentum

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
abbrev Zed (n:ℕ): ℕ:= 4+2*n
abbrev L (n:ℕ):= Fin (Zed n)
abbrev SectorP (n:ℕ):= Momentum (L n)
abbrev GlyphA (m n:ℕ): ℕ:= 2*(n-m)
abbrev Apart (m n:ℕ):= Fin (GlyphA m n)
variable {m n i:ℕ}
lemma op (h:m≤n): Zed m+GlyphA m n=Zed n:=by unfold Zed GlyphA; omega
def rises (h:m≤n): L m ↪ L n:= ⟨fun i=> ⟨i.val, by have ht:=i.isLt; unfold Zed at *; omega⟩,fun i j (he)=>Fin.ext (congr_arg (Fin.val (n:=Zed n)) he)⟩
def aside (h:m≤n): Apart m n ↪ L n:= ⟨fun i=>⟨Zed m+i.val,by rw [← op h]; have hx:=i.isLt; omega⟩,by intro i j he; obtain hh:= congr_arg Fin.val he; exact Fin.ext (Nat.add_left_cancel hh)⟩
variable {A B R:Type} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
def spray (i:A): Momentum A:= Pi.single i 1
def sendB (f:A↪B): Momentum A→L[ℝ] Momentum B:= ∑ i:A,(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:A=>ℝ) i).smulRight (spray (f i))
end YM.MS.Arts
