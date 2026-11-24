import YM.Integration.WilsonThermometerPepperCapture

/- The whole physical chamber and its single shifted value recover a proper
   raw face on the original support, including when that face omits the center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPepperFace
open Finset Marker MergeProof MergeProof.Accent MergeProof.Ribbons Extra.Trajectories
open scoped BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]
local notation "J" => Stock.census I

def whole (I:Type)[Fintype I][DecidableEq I]:(Stock.census I).Mode:=⟨univ,mem_univ _⟩
def rest (s:(J).Mode):(J).Mode:=⟨univ \ s.val,mem_univ _⟩

def scalar (a:I)(c:ℂ)(i:I):ℂ:=if i=a then c else 0

def atSite (a:I):Fibers I Unit:=⟨fun _=>(),fun _=>a,fun _=>rfl⟩

theorem home (a:I)(f:Poly (J)):
    (Fibers.reap (atSite a) f).part ((Stock.census Unit).fire ())=f.part (whole I):=by
  change f.part ((atSite a).plena _)=_
  congr 1
  apply Subtype.ext
  ext i
  rw [Fibers.reaped]
  change ()∈({()}:Finset Unit) ↔ i∈(univ:Finset I)
  simp

private theorem boundary (s t:(J).Mode):Poly.merges s t (whole I) ↔ t=rest s:=by
  constructor
  · rintro ⟨dis,cover⟩
    apply Subtype.ext
    ext i
    change i∈t.val ↔ i∈univ \ s.val
    simp only [mem_sdiff,mem_univ,true_and]
    constructor
    · exact fun h k=>disjoint_left.mp dis k h
    · intro outside
      have all:i∈s.val∪t.val:=by rw [cover];exact mem_univ _
      exact (mem_union.mp all).resolve_left outside
  · rintro rfl
    refine ⟨disjoint_left.mpr (fun _ hi hx=>(mem_sdiff.mp hx).2 hi),?_⟩
    ext i
    change i∈s.val∪(univ \ s.val) ↔ i∈univ
    simp only [mem_union,mem_sdiff,mem_univ,true_and,or_not]

theorem reading (a:I)(c:ℂ)(f:Poly (J)):
    (Poly.pass (Mach (J) (scalar a c))*f).part (whole I)=
      f.part (whole I)+c*f.part (rest ((J).fire a)):=by
  classical
  have monomial:Mach (J) (scalar a c)=Poly.send ((J).fire a) c:=by
    unfold Mach
    rw [sum_eq_single a]
    · simp [scalar]
    · intro j _ away
      simp [scalar,away]
    · simp
  rw [monomial,pass_send (show ((J).fire a).val.Nonempty from singleton_nonempty _) c,
    add_mul,one_mul,Poly.part_plus]
  congr 1
  simp only [Poly.part_mul,boundary,sum_ite_eq',mem_univ,if_true]
  rw [sum_eq_single ((J).fire a)]
  · simp [Poly.part_send]
  · intro j _ apart
    simp [Poly.part_send,apart]
  · simp

omit [Fintype I] in
theorem affordable (w:I→ℝ)(pos:∀i,0<w i)(a:I):
    ∀i,w i * ‖scalar a ((2*w a)⁻¹:ℝ) i‖≤1/2:=by
  intro i
  by_cases same:i=a
  · subst i
    have sign:0<2*w a:=mul_pos (by norm_num) (pos a)
    have price:scalar a ((2*w a)⁻¹:ℝ) a=((2*w a)⁻¹:ℝ):=if_pos rfl
    rw [price,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr sign)]
    apply le_of_eq
    field_simp [(pos a).ne']
  · simp [scalar,same]

end YM.Integration.WilsonThermometerPepperFace
end
