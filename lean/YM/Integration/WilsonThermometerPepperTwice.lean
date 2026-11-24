import YM.Integration.WilsonThermometerPepperFace
/- The whole physical chamber and its single shifted value recover a proper
   raw face on the original support, including when that face omits the center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPepperTwice
open Finset Marker MergeProof MergeProof.Accent MergeProof.Ribbons Extra.Trajectories
open scoped BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]
local notation "J" => Stock.census I

open WilsonThermometerPepperFace

def stripped (s:(J).Mode)(a:I):(J).Mode:=⟨s.val.erase a,mem_univ _⟩

private theorem complement (a:I)(s t:(J).Mode)(has:a∈s.val):
    Poly.merges ((J).fire a) t s ↔ t=stripped s a:=by
  constructor
  · rintro ⟨dis,union⟩
    apply Subtype.ext
    ext i
    change i∈t.val ↔ i∈s.val.erase a
    simp only [mem_erase]
    constructor
    · intro hi
      have apart:i≠a:=by
        rintro rfl
        exact disjoint_left.mp dis (mem_singleton_self _) hi
      refine ⟨apart,?_⟩
      rw [←union]
      exact mem_union_right _ hi
    · rintro ⟨hne,hi⟩
      rw [←union] at hi
      exact (mem_union.mp hi).resolve_left (fun h=>hne (mem_singleton.mp h))
  · rintro rfl
    refine ⟨disjoint_left.mpr (fun i h hx=>(mem_erase.mp hx).1 (mem_singleton.mp h)),?_⟩
    change ({a}:Finset I)∪s.val.erase a=s.val
    rw [singleton_union,insert_erase has]

theorem at_mask (a:I)(c:ℂ)(s:(J).Mode)(has:a∈s.val)(f:Poly (J)):
    (Poly.pass (Mach (J) (scalar a c))*f).part s=f.part s+c*f.part (stripped s a):=by
  have single:Mach (J) (scalar a c)=Poly.send ((J).fire a) c:=by
    unfold Mach
    rw [sum_eq_single a]
    · simp [scalar]
    · intro i _ h
      simp [scalar,h]
    · simp
  rw [single,pass_send (show ((J).fire a).val.Nonempty from singleton_nonempty _) c,add_mul,one_mul,Poly.part_plus]
  congr 1
  rw [Poly.part_mul,sum_eq_single ((J).fire a)]
  · simp only [Poly.part_send,complement a s _ has,sum_ite_eq',mem_univ,if_true]
  · intro i _ h
    simp [Poly.part_send,h]
  · simp

def joined (a b:I)(ca cb:ℂ)(i:I):ℂ:=scalar a ca i+scalar b cb i

theorem together (a b:I)(apart:b≠a)(x y:ℂ)(f:Poly (J)):
    (Poly.pass (Mach (J) (joined a b x y))*f).part (whole I)=
      (f.part (whole I)+y*f.part (rest ((J).fire b)))+
        x*(f.part (rest ((J).fire a))+y*f.part (stripped (rest ((J).fire a)) b)):=by
  have addition:Mach (J) (joined a b x y)=Mach (J) (scalar a x)+Mach (J) (scalar b y):=by
    simp only [Mach,joined,send_add,sum_add_distrib]
  have has:b∈(rest ((J).fire a)).val:=mem_sdiff.mpr ⟨mem_univ _,fun h=>apart (mem_singleton.mp h)⟩
  rw [addition,pass_add (mute (J) _) (mute (J) _),mul_assoc,reading,reading,at_mask _ _ _ has]

omit [Fintype I] in
theorem affordable (a b:I)(apart:b≠a)(w:I→ℝ)(p:∀i,0<w i):
  ∀i,w i*‖joined a b ((2*w a)⁻¹:ℝ) ((2*w b)⁻¹:ℝ) i‖≤1/2:=by
  intro i
  by_cases hi:i=a
  · have other:i≠b:=hi ▸ Ne.symm apart
    have cancel:scalar b (((2*w b)⁻¹:ℝ):ℂ) i=0:=if_neg other
    rw [joined,cancel,add_zero]
    exact WilsonThermometerPepperFace.affordable w p a i
  · have cancel:scalar a (((2*w a)⁻¹:ℝ):ℂ) i=0:=if_neg hi
    rw [joined,cancel,zero_add]
    exact WilsonThermometerPepperFace.affordable w p b i
end YM.Integration.WilsonThermometerPepperTwice
end
