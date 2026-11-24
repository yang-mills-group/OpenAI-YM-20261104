import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reports
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.PublicAxes
open YM YM.Maxwell.Free
open scoped Classical BigOperators

theorem original (σ:Equiv.Perm Axis)(c:Axis→ℝ)(U:E4≃ₗᵢ[ℝ]E4)
    (sign:∀a,c a=1 ∨ c a= -1)(basisMove:∀a,U (basis a)=c a • basis (σ a)):
    ∃s:Signed,s.perm=σ ∧ tilt s=c ∧ Ortho.motion s.ortho=U:=by
  classical
  let s:Signed:=⟨σ,fun a=>decide (c a = -1)⟩
  have weights:tilt s=c:=by
    funext a
    rcases sign a with pos|neg
    · norm_num [s,tilt,pos]
    · simp [s,tilt,neg]
  refine ⟨s,rfl,weights,?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  have expand:(∑ a:Axis,x a • basis a)=x:=by
    apply PiLp.ext
    intro j
    simp [basis_eq]
  conv_lhs=>rw [←expand,map_sum]
  conv_rhs=>rw [←expand,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul,Ortho.motion_at,heads,weights,basisMove]
end IssuedMaxwell.PublicAxes
end
