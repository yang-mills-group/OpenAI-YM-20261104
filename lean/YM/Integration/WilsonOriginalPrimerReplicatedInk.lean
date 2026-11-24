import YM.Integration.WilsonOriginalPrimerReplicatedFields

/-! Before the integral, all copies of one issued letter form one
additive primary chart on the genuine enlarged torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerReplicatedInk
open Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Marker QuadraticLocal QuadraticLocal.Earn FVA1Physical.TwoReset PowerSeries
open scoped Classical BigOperators

variable {G:Gauge}{n n':Side}{d:ℕ}{Y:Type}
variable (T:Y→PChart G n')(shell:∀y,shellK d (T y))(pure:∀y,∀i,Pure (T y i))
include shell pure

theorem assembled (s:Finset Y):
    shellK d (∑u∈s,T u) ∧ (∀i,Pure ((∑u∈s,T u) i)) ∧
      flash (∑u∈s,T u)=∑u∈s,flash (T u):=by
  induction s using Finset.induction with
  | empty=>
    simp only [Finset.sum_empty]
    have h0:shellK d (0:PChart G n'):=fun _ _ _=>rfl
    refine ⟨h0,fun _=>Pure.zero,?_⟩
    apply add_left_cancel (a:=flash (0:PChart G n'))
    simpa only [add_zero,zero_add] using (flash_add (finite_shell h0) (finite_shell h0)).symm
  | insert u s hu ih=>
    simp only [Finset.sum_insert hu]
    exact ⟨shell_sum (shell u) ih.1,fun i=>(pure u i).add (ih.2.1 i),
      by rw [flash_add (finite_shell (shell u)) (finite_shell ih.1),ih.2.2]⟩

variable (h:n.val∣n'.val)(o:Site n)(T₀:Site n'→PChart G n')

def located :PChart G n':=∑u:Fin (Pages n n'),T₀ (page h o u).val

omit shell pure in
theorem sheets (hs:∀x,shellK d (T₀ x))(hp:∀x,∀i,Pure (T₀ x i)):
    shellK d (located h o T₀) ∧ (∀i,Pure (located h o T₀ i)) ∧
      flash (located h o T₀)=∑u:Fin (Pages n n'),flash (T₀ (page h o u).val):=
  assembled (fun u:Fin (Pages n n')=>T₀ (page h o u).val) (fun _=>hs _) (fun _=>hp _) Finset.univ

end YM.Integration.WilsonOriginalPrimerReplicatedInk
end
