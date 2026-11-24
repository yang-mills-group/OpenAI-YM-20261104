import YM.Integration.WilsonPhysicalHistoryKtoneNames

/-! Read the product at the genuine mixed label without discarding its two proper partitions. -/
noncomputable section
open scoped BigOperators Classical
namespace YM.Integration.WilsonPhysicalHistoryKtone
open Finset Marker

private theorem catalogue:(Finset.univ:Finset pairBook.Mode)=
    {pairBook.quiet,pairBook.fire false,pairBook.fire true,pairMode}:=by
  ext s
  simp only [mem_univ,true_iff,mem_insert,mem_singleton]
  by_cases f:false∈s.val <;> by_cases t:true∈s.val
  · right;right;right
    apply Subtype.ext
    ext v;cases v <;> simp [pairMode,f,t]
  · right;left
    apply Subtype.ext
    ext v;cases v <;> simp [Census.fire,f,t]
  · right;right;left
    apply Subtype.ext
    ext v;cases v <;> simp [Census.fire,f,t]
  · left
    apply Subtype.ext
    ext v;cases v <;> simp [Census.quiet,f,t]

theorem mode_sum {A:Type*}[AddCommMonoid A](F:pairBook.Mode→A):
    ∑s,F s=F pairBook.quiet+(F (pairBook.fire false)+(F (pairBook.fire true)+F pairMode)):=by
  rw [catalogue]
  simp (disch:=decide) only [Finset.sum_insert,Finset.sum_singleton]

theorem joined_mul (P Q:Poly pairBook):
    (P*Q).part pairMode=P.part pairBook.quiet*Q.part pairMode+
      P.part (pairBook.fire false)*Q.part (pairBook.fire true)+
      P.part (pairBook.fire true)*Q.part (pairBook.fire false)+
      P.part pairMode*Q.part pairBook.quiet:=by
  rw [Poly.part_mul,mode_sum]
  simp only [mode_sum]
  simp (disch:=decide) only [if_pos,if_neg,add_zero,zero_add]
  ring

end YM.Integration.WilsonPhysicalHistoryKtone
