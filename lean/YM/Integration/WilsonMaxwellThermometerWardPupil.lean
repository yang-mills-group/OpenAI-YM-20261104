import YM.Integration.WilsonMaxwellThermometerWardColors
import YM.PertExtension.BareWords

/-! The quadratic projection of an arbitrary filed coordinate on its
own original section. All omitted occupied entries have radial order three. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardPupil
open Function Set Filter Finset Lattice Labels Source Wilson
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series
open Series.Radial Series.Tested
open scoped Classical BigOperators
variable {G:Gauge} {d:ℕ} {F:Frame G d} (C:SectionData F)
    (c:F.Coeff) (L:ℂ→L[ℝ]ℝ) {n:Side} (o:Site n)

def selected (s:Finset F.Index) (U:Config G n) :=
  ∑ i∈s,L (c i)*fieldAt C i o U

def active:Finset F.Index:=univ.erase 0
def next:Finset F.Index:=univ.filter (fun i=>(F.grades i).2=2)
def later:Finset F.Index:=univ.filter (fun i=>3≤(F.grades i).2)

theorem literal {H:Hol G} (sound:C.Sound H) (U:Config G n):
    L (C.places c o U) = L (c 0) + selected C c L o (active (F:=F)) U := by
  classical
  have split:c = ∑i:F.Index, c i • Pi.single i (1:ℂ) := by
    funext k
    simp [Pi.single_apply,Finset.sum_apply]
  have pieces:L (C.places c o U)=∑i:F.Index,L (c i)*fieldAt C i o U := by
    conv_lhs => rw [split]
    unfold SectionData.places SectionData.evaluate
    simp only [map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro i _
    change L (c i * C.places (Pi.single i 1) o U)=_
    rw [←scalar_real sound]
    rw [mul_comm (c i),←Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  rw [pieces, ←Finset.add_sum_erase (univ : Finset F.Index) (fun i=>L (c i)*fieldAt C i o U) (mem_univ 0)]
  simp [unit_zero sound,selected,active]

theorem split (simple:G.Simple) (U:Config G n):
    selected C c L o (active (F:=F)) U =
      selected C c L o (next (F:=F)) U + selected C c L o (later (F:=F)) U:=by
  have subset : active (F:=F) = next (F:=F)∪later (F:=F):=by
    apply Finset.ext
    intro i
    rw [active,next,later, Finset.mem_union, Finset.mem_erase,Finset.mem_filter,Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,and_true]
    have gap:=WilsonMaxwellThermometerWardColors.arity simple F i
    by_cases hi:i=0
    · subst i; simp [F.zero_degree]
    · have h:=F.factors_pos i hi
      constructor
      · intro _; omega
      · exact fun _=>hi
  have dis:Disjoint (next (F:=F)) (later (F:=F)):=by
    rw [Finset.disjoint_left]
    intro i hi hl
    have a:=(mem_filter.mp hi).2
    have b:=(mem_filter.mp hl).2
    omega
  rw [selected,subset,sum_union dis]; rfl

theorem radial {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C) (s:Finset F.Index)
    (k:ℕ) (floor:∀i∈s,k≤(F.grades i).2):
    RadialOrder k (fun x:Dir G n=>selected C c L o s (representative x)):=by
  intro x
  let term:=fun i:F.Index=>fun t:ℝ=>L (c i)*fieldAt C i o (representative (t • x))
  have h(i)(hi:i∈s):Bill k (term i):=by
    have h0:=(pre_field C sound pop i o).2 x
    obtain ⟨N,non,hn⟩:=bill_ge h0 (floor i hi)
    refine ⟨‖L (c i)‖*N, mul_nonneg (norm_nonneg _) non, hn.mono fun t fee=>?_⟩
    change ‖L (c i)*fieldAt C i o (representative (t • x))‖≤_
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left fee (norm_nonneg _)
  convert! bill_sum s term h using 1
  funext t
  simp [selected,term,Finset.sum_apply]

theorem costs {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C) (simple:G.Simple):
    RadialOrder 2 (fun x:Dir G n=>selected C c L o (active (F:=F)) (representative x)) ∧
    RadialOrder 3 (fun x:Dir G n=>selected C c L o (later (F:=F)) (representative x)) := by
  constructor
  · apply radial C c L o sound pop
    intro i hi
    have hp:=F.factors_pos i (mem_erase.mp hi).1
    have hn:=WilsonMaxwellThermometerWardColors.arity simple F i
    omega
  · exact radial C c L o sound pop _ _ (fun i hi=>(mem_filter.mp hi).2)

end YM.Integration.WilsonMaxwellThermometerWardPupil
