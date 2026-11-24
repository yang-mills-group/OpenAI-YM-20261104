import YM.Integration.WilsonPositionProgramTrialFixedDigits

/-! A composite parent is the successive native centered parent. Oddness of
the original block is used at the boundary of the signed representative. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialNestedCenters
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialCellDigits WilsonPositionProgramTrialFixedDigits
open scoped Classical

theorem combine (A B C : Side) (size : C.val=B.val*A.val) (odd : Odd A.val) (x : Cover) :
    parentC C x=parentC A (parentC B x) := by
  let y := parentC B x
  let z := parentC A y
  let a := lift (wrap A y)
  let b := lift (wrap B x)
  let t := B.val • a+b
  have center : lift (wrap C t)=t := by
    apply lift_eq_iff.mpr
    refine ⟨rfl,?_⟩
    intro i
    obtain ⟨k,hk⟩:=odd
    have ar:=lift_centers (wrap A y) i
    have br:=lift_centers (wrap B x) i
    have hk' : (A.val:ℤ)=2*(k:ℤ)+1 := by exact_mod_cast hk
    have ah : -(A.val:ℤ)+1≤2*a i ∧ 2*a i≤(A.val:ℤ)-1 := by
      dsimp only [a]; omega
    have bh : -(B.val:ℤ)<2*b i ∧ 2*b i≤(B.val:ℤ) := br
    have pos : (0:ℤ)<B.val := by exact_mod_cast B.2
    change -(C.val:ℤ)<2*(B.val • a i+b i) ∧ 2*(B.val • a i+b i)≤(C.val:ℤ)
    rw [size,Nat.cast_mul,nsmul_eq_mul]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ah.1 pos.le]
    · nlinarith [mul_le_mul_of_nonneg_left ah.2 pos.le]
  have eq : C.val • z+lift (wrap C t)=x := by
    rw [center,size,mul_smul]
    change B.val • (A.val • z)+(B.val • a+b)=x
    rw [←add_assoc,←smul_add,show A.val • z+a=y from packed A y]
    exact packed B x
  calc parentC C x = parentC C (C.val • z+lift (wrap C t)) := congrArg (parentC C) eq.symm
       _ = z := congrArg Prod.fst ((panel C Unit).symm_apply_apply (z,wrap C t,()))

theorem one (x : Cover) : parentC 1 x=x := by
  have h:=packed 1 x
  have residue : lift (wrap 1 x) = 0 := by
    funext i
    have bound:=lift_centers (wrap 1 x) i
    change -(1:ℤ) < 2*lift (wrap 1 x) i ∧ 2*lift (wrap 1 x) i≤1 at bound
    change lift (wrap 1 x) i=0
    omega
  simpa [residue] using h

theorem course {G:Gauge} {I:Type} (L:Levels G) {c j K:ℕ} (start:c≤j) (step:j<K) (o : I → Cover) :
    (fun i => (L.S.block j).val • parents L.S step.le o i + lift (cells L c K o j i)) =
      parents L.S step o := by
  funext i
  let A:= L.S.block j
  let B:= (L.S.toDepth step 0).count
  let C:= (L.S.toDepth step.le 0).count
  have size : C.val=B.val*A.val :=
    Next.Rank.Station.size_comp (L.S.oneStep j 0) (L.S.toDepth step 0) _
  have mid:=combine A B C size (L.S.block_odd j) (o i)
  simp only [cells,dif_pos (show c≤j ∧ j<K from ⟨start,step⟩)]
  change A.val • parentC C (o i)+lift (wrap A (parentC B (o i)))=parentC B (o i)
  rw [mid,packed]

end YM.Integration.WilsonPositionProgramTrialNestedCenters
