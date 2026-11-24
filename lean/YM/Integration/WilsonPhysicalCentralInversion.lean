import YM.FrontierTrace.Primary.HorizonFour

/-! Central coordinate inversion on the actual radial Wilson label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCentralInversion
open Function Labels Maxwell Analysis
open scoped BigOperators Classical Topology
variable {G:Gauge}

def inversion : Signed := ⟨Equiv.refl _, fun _ => true⟩
abbrev flip:=inversion.ortho

lemma entry (i j:Axis):flip.val i j = if j=i then -1 else 0:=by rfl

lemma move (x:E4):Ortho.move flip x= -x:=by
  ext i
  change ∑ j:Axis,flip.val i j*x j = -(x i)
  simp [entry,ite_mul]

lemma backwards (x:E4):Ortho.move flip⁻¹ x= -x:=by
  have h:=Ortho.move_inv flip x
  rw [move] at h
  simpa using congrArg Neg.neg h

lemma inverse:flip⁻¹=flip:=by
  apply Subtype.ext
  ext i j
  rw [←M4.move_basis (flip⁻¹).val i j,←M4.move_basis flip.val i j]
  exact congrArg (fun y:E4=>y i) ((backwards (basis j)).trans (move (basis j)).symm)

theorem turns {j:ℕ}(A:Taylor G j):
    Taylor.turn flip A = ((-1:ℝ)^(j+2)) • A:=by
  apply Taylor.value_ext
  funext i x
  have scale:=A.value_hom i x (-1:ℝ)
  rw [neg_one_smul] at scale
  rw [Taylor.turn_value,backwards]
  change ∑ k:Axis,flip.val i k • A.value k (-x) = ((-1:ℝ)^(j+2)) • A.value i x
  simp only [entry,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [scale,smul_smul]
  congr 1
  ring

theorem even_jet (A:Taylor G 0):Taylor.turn flip A=A:=by
  rw [turns];norm_num

theorem odd_jet (A:Taylor G 1):Taylor.turn flip A= -A:=by
  rw [turns];norm_num; exact neg_one_smul ℝ A

end YM.Integration.WilsonPhysicalCentralInversion
end
