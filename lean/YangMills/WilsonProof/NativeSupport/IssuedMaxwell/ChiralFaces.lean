import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleAxes
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.ChiralFaces
open YM YM.Lattice YM.XSpace YM.XSpace.Chiral YM.Maxwell.Free
open scoped BigOperators
private def charge (s:Bool)(i:Fin 3)(a b:Axis):ℤ:=
  if a=0 ∧ b=i.succ then 1 else
  if a=(i+1).succ ∧ b=(i+2).succ then (if s then 1 else -1) else
  if a=(i+2).succ ∧ b=(i+1).succ then (if s then -1 else 1) else 0
private theorem sheet : ∀s i (b:PlaqAxes),triCoeff s i (six b) (endr b)=charge s i (six b) (endr b):=by decide
private def face (a b:Axis)(h:a<b):PlaqAxes:=⟨(a,b),h⟩
private theorem full : (Finset.univ:Finset PlaqAxes)=
    {face 0 1 (by decide),face 0 2 (by decide),face 0 3 (by decide),
     face 1 2 (by decide),face 1 3 (by decide),face 2 3 (by decide)}:=by decide

private theorem listed (h:PlaqAxes→ℝ) : (∑b,h b)=
    h (face 0 1 (by decide))+(h (face 0 2 (by decide))+(h (face 0 3 (by decide))+
    (h (face 1 2 (by decide))+(h (face 1 3 (by decide))+h (face 2 3 (by decide)))))):=by
  rw [full]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

theorem original (s:Bool)(i:Fin 3)(F:Axis→Axis→ℝ)(skew:∀a b,F a b= -F b a):
    (∑ b:PlaqAxes,q s i (six b) (endr b)*F (six b) (endr b))=
    (if s then F 0 i.succ+F (i+1).succ (i+2).succ else F 0 i.succ-F (i+1).succ (i+2).succ):=by
  simp only [q,sheet,listed]
  fin_cases i <;> cases s <;> norm_num [face,charge,six,endr] <;>
    simp (config := {decide := true}) <;>
    first | rfl | linarith [skew 1 3,skew 3 1]
end IssuedMaxwell.ChiralFaces
end
