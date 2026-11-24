import YM.Overlay.Terminal
import YM.Comparison.RG02.Cumulants.Parents
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Read the full normalized logarithm as the actual seven-position Rose
polynomial on the same capped thermometer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredScalar
open Finset Marker Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def face (s : Finset (Fin 3)) : (J).Mode := ⟨s,mem_univ _⟩
def read (P : Poly J) (s : Finset (Fin 3)) := P.part (face s)

private def names : (J).Mode ≃ Finset (Fin 3) :=
  ⟨Subtype.val,face,fun _ => rfl,fun _=>rfl⟩

private theorem merged (a b : (J).Mode) (s : Finset (Fin 3)) :
    Poly.merges a b (face s) ↔ a.val ⊆ s ∧ b=face (s \ a.val) := by
  constructor
  · rintro ⟨dis,cover⟩
    change a.val∪b.val=s at cover
    refine ⟨cover ▸ subset_union_left,Subtype.ext ?_⟩
    ext i
    change i∈b.val ↔ i∈s \ a.val
    rw [←cover,mem_sdiff,mem_union]
    constructor
    · intro hi
      exact ⟨Or.inr hi,fun ha => disjoint_left.mp dis ha hi⟩
    · rintro ⟨h,ha⟩
      exact h.resolve_left ha
  · rintro ⟨sub,rfl⟩
    exact ⟨disjoint_left.mpr (fun i hi hit => (mem_sdiff.mp hit).2 hi),
      (union_comm ..).trans (sdiff_union_of_subset sub)⟩

private theorem products (P Q : Poly J) (s : Finset (Fin 3)) :
    read (P*Q) s = ∑ a∈s.powerset, read P a*read Q (s \ a) := by
  simp only [read,Poly.part_mul,merged,ite_and]
  have each (a : (J).Mode) :
      (∑ b : (J).Mode, if a.val⊆s then if b=face (s\a.val) then P.part a*Q.part b else 0 else 0)=
      if a.val⊆s then P.part a * Q.part (face (s\a.val)) else 0 := by
    by_cases h : a.val⊆s <;> simp [h]
  simp_rw [each]
  calc
    _ = ∑ a : Finset (Fin 3), if a⊆s then P.part (face a)*Q.part (face (s\a)) else 0 :=
      Fintype.sum_equiv names _ _ (fun _=>rfl)
    _ = _ := by
      rw [←sum_filter]
      congr 1
      ext a
      simp only [mem_filter,mem_univ,true_and,mem_powerset]

private theorem rooted (P : Poly J) (unit : P.part (J).quiet=1) (i : Fin 3)
    (s : Finset (Fin 3)) (h : i∈s) :
    read P s=∑ a∈s.powerset, (if i∈a then read (Extra.Trajectories.connected P) a else 0)*read P (s\a) := by
  have law := congrArg (fun x : Poly J=>read x s) (moment_root i P unit)
  rw [mul_comm,products] at law
  simpa only [read,highlight_part,face,h,if_true] using law

private theorem occupied : (univ : Finset (Fin 3)).powerset.filter (fun s => (0:Fin 3)∈s) =
      {{0},{0,1},{0,2},univ} := by
  ext s
  simp only [mem_filter,mem_powerset,subset_univ,true_and,mem_insert,mem_singleton]
  constructor
  · intro h0
    by_cases h1 : 1∈s <;> by_cases h2 : 2∈s
    · right; right; right
      ext i
      fin_cases i <;> simp [h0,h1,h2]
    · right; left
      ext i
      fin_cases i <;> simp [h0,h1,h2]
    · right; right; left
      ext i
      fin_cases i <;> simp [h0,h1,h2]
    · left
      ext i
      fin_cases i <;> simp [h0,h1,h2]
  · rintro (rfl|rfl|rfl|rfl) <;> simp

/-- The full three-name log, on ordinary scalar moments. -/
theorem three (P : Poly J) (unit : P.part (J).quiet=1) :
    read (Extra.Trajectories.connected P) univ =
      read P univ - (read P {0,1}*read P {2}+read P {0,2}*read P {1}+
        read P {1,2}*read P {0})+2*(read P {0}*read P {1}*read P {2}) := by
  let K := Extra.Trajectories.connected P
  let summand (s : Finset (Fin 3)) := read K s * read P (univ \ s)
  have germ := rooted P unit 0 univ (mem_univ _)
  have turn (s : Finset (Fin 3)) :
      (if (0:Fin 3)∈s then read K s else 0)*read P (univ \ s) =
        if 0∈s then summand s else 0 := by
    by_cases h : (0:Fin 3)∈s <;> simp [h,summand]
  change read P univ = ∑ s∈(univ:Finset (Fin 3)).powerset,
    (if (0:Fin 3)∈s then read K s else 0)*read P (univ \ s) at germ
  simp_rw [turn] at germ
  rw [←Finset.sum_filter,occupied] at germ
  have a : ({0}: Finset (Fin 3))∉({{0,1},{0,2},univ}:Finset (Finset (Fin 3))) := by decide
  have b : ({0,1}: Finset (Fin 3))∉({{0,2},univ}:Finset (Finset (Fin 3))) := by decide
  have c : ({0,2}: Finset (Fin 3))∉({univ}:Finset (Finset (Fin 3))) := by decide
  rw [sum_insert a,sum_insert b,sum_insert c,sum_singleton] at germ
  have d₀ : (univ:Finset (Fin 3)) \ {0}={1,2} := by decide
  have d₁ : (univ:Finset (Fin 3)) \ {0,1}={2} := by decide
  have d₂ : (univ:Finset (Fin 3)) \ {0,2}={1} := by decide
  have tiny : read P (⊥ : Finset (Fin 3))=1 := unit
  have one : read K {0}=read P {0} := lamp 0 P unit
  have two (i : Fin 3) (hi : (0:Fin 3)≠i) :
      read K {0,i} = read P {0,i}-read P {0}*read P {i} :=
    twins 0 i (face {0,i}) P unit hi rfl
  simp only [summand,d₀,d₁,d₂,sdiff_self,tiny,mul_one,one,two 1 (by decide),two 2 (by decide)] at germ
  change read K univ=_
  linear_combination -germ

end YM.Integration.WilsonThermometerCenteredScalar
