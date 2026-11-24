import YangMills.WilsonProof.NativeSupport.MarkerSubstitution
import YangMills.WilsonProof.NativeSupport.JointSound

/-! Put the blocking tests on the very same forest tag that occurs in the
fine density.  At a fixed tag and pair of fields this amounts to a diagonal
substitution in the original full marker algebra, even for dirty tickets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Finset Marker Extra.Trajectories Packet MarkerSubstitution
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V]
local notation "B" => Stock.census V

def letter (a : V → ℂ) (i : V) : Poly B := Poly.send (tag {i}) (a i)

private theorem null (a : V → ℂ) (i : V) : letter a i * letter a i = 0 := by
  by_contra h
  obtain ⟨_, hd, _⟩ := merges_of_tagged_mul h
  exact disjoint_left.mp hd (mem_singleton_self i) (mem_singleton_self i)

def diagonal (a : V → ℂ) : Poly B →+* Poly B := hom (letter a) (null a)

private theorem letters (a : V → ℂ) (S : Finset V) :
    ∏ i∈S, letter a i = Poly.send (tag S) (∏ i∈S, a i) := by
  induction S using Finset.induction with
  | empty =>
    simp only [prod_empty]
    ext p
    rw [Poly.one_part, Poly.part_send]
    rfl
  | @insert i S hi ih =>
    rw [prod_insert hi,prod_insert hi,ih]
    exact tagged_mul (tag {i}) (tag S) (tag (insert i S)) ⟨Finset.disjoint_singleton_left.mpr hi,by change {i} ∪ S = insert i S; simp⟩ _ _

theorem on_monomial (a : V → ℂ) (S : Finset V) (c : ℂ) :
    diagonal a (Poly.send (tag S) c) = (∏ i∈S,a i) • Poly.send (tag S) c := by
  change applyTo _ _=_
  rw [on_send,letters]
  ext p
  simp only [Poly.part_smul,Poly.part_send]
  split <;> ring

theorem on_part (a : V → ℂ) (P : Poly B) (S : Finset V) :
    (diagonal a P).part (tag S)=(∏ i∈S,a i)*P.part (tag S) := by
  change (applyTo _ _).part _=_
  simp only [applyTo,Poly.part_sum,letters,Poly.part_smul,Poly.part_send]
  rw [sum_eq_single S]
  · rw [if_pos rfl]
    ring
  · intro T _ h
    rw [if_neg (fun e=>h (congrArg Subtype.val e).symm)]
    ring
  · simp

theorem untouched (fresh : Finset V) (a : V → ℂ) (old : ∀ i,i∉fresh → a i=1)
    (P : Poly B) (ages : ∀ S : Finset V, P.part (tag S) ≠ 0 → Disjoint S fresh) :
    diagonal a P=P := by
  ext p
  let S := p.val
  change (diagonal a P).part (tag S) = P.part (tag S)
  rw [on_part]
  by_cases h : P.part (tag S)=0
  · rw [h,mul_zero]
  have eq : ∏ i∈S,a i = 1 := prod_eq_one fun i hi=>old i (disjoint_left.mp (ages S h) hi)
  rw [eq,one_mul]

end YM.Integration.InletSusceptibility.JointShadow
