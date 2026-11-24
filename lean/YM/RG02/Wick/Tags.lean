import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Pi
import YM.RG.Block

/-!
# Summation over tags

Passing covariance lines through cumulants will use this TEST for disjoint
factorization. The familiar product law supplies it automatically; a generic
law on dependent tags may not. In particular for the complete real side
Wilson step don't pretend that all predictor choices in density are an
independent uniform law. Nor that overlapping copies of the same predictor
read are separate tag occurrences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick.Actor
open Function Finset
open scoped BigOperators Classical
variable {I : Type} {D : I → Type}

abbrev Draw {I : Type} (D : I → Type) := (i : I) → D i

def Needs (f : Draw D → ℂ)(s : Finset I) := ∀ x y : Draw D,(∀ i∈s,x i=y i) → f x=f y
namespace Needs
variable {s t : Finset I}{f g : Draw D → ℂ}
lemma enlarge (h : Needs f s)(he : s ⊆ t) : Needs f t := fun x y hh => h x y fun i hi => hh i (he hi)
lemma sum (h : Needs f s)(he : Needs g s) : Needs (f+g) s := fun x y hh => congr_arg₂ (·+·) (h x y hh) (he x y hh)
lemma mul (h : Needs f s)(he : Needs g s) : Needs (f*g) s := fun x y hh => congr_arg₂ (·*·) (h x y hh) (he x y hh)
lemma product {ι : Type*}{c : Finset ι}{u : ι → Draw D → ℂ}(H : ∀ i∈c,Needs (u i) s) : Needs (∏ i∈c,u i) s :=
  fun x y hh => by simp only [Finset.prod_apply]; exact prod_congr rfl (fun i hi => H i hi x y hh)
lemma sums {ι : Type*}{c : Finset ι}{u : ι → Draw D → ℂ}(H : ∀ i∈c,Needs (u i) s) : Needs (∑ i∈c,u i) s :=
  fun x y hh => by simp only [Finset.sum_apply]; exact sum_congr rfl (fun i hi => H i hi x y hh)
end Needs

def Multiplying (μ : (Draw D → ℂ)→ₗ[ℂ]ℂ) := μ 1=1 ∧ ∀ s t : Finset I, Disjoint s t →
    ∀ f g : Draw D → ℂ, Needs f s → Needs g t → μ (f*g)=μ f*μ g

section finite
variable [DecidableEq I] [Fintype I] [∀ i,Fintype (D i)]

/-- Any finite average. -/
def mean {T : Type*}[Fintype T](p : T → ℂ) : (T → ℂ)→ₗ[ℂ]ℂ where
  toFun v := ∑ i,p i*v i
  map_add' v w := by simp [mul_add,sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_sum]
    exact sum_congr rfl fun i _ => mul_left_comm ..

def joint (p : (i : I) → D i → ℂ)(t : Draw D) : ℂ := ∏ i : I,p i (t i)
def expectation (p : (i : I) → D i → ℂ) : (Draw D → ℂ)→ₗ[ℂ]ℂ := mean (joint p)

private def trades (s : Finset I) : Equiv.Perm (Draw D × Draw D) :=
  let T (w : Draw D × Draw D) := (((fun i : I => if i∈s then w.2 i else w.1 i) : Draw D),
      ((fun i : I => if i∈s then w.1 i else w.2 i) : Draw D))
  have h : T ∘ T=id := by
    funext w; apply Prod.ext <;> funext i <;> by_cases h : i∈s <;> simp only [T,id_eq,comp_apply,h,↓reduceIte]
  ⟨T,T,congr_fun h,congr_fun h⟩

lemma contracting (p : (i : I)→ D i → ℂ)(hp : ∀ i, ∑ a,p i a=1) :
    Multiplying (expectation p) := by
  have hs : ∑ i,joint p i=1 := by
    unfold joint; rw [← Fintype.prod_sum]; simp_rw [hp,prod_const_one]
  constructor
  · change ∑ i, joint p i * (1 : Draw D → ℂ) i=1
    simpa using hs
  intro s t hu f g Hf Hg
  let μ := expectation p
  let a (v : Draw D × Draw D) := joint p v.1 * joint p v.2 * f v.1 * g v.1
  let b (v : Draw D × Draw D) := (joint p v.2*f v.2) * (joint p v.1*g v.1)
  let e := trades (D:=D) s
  have he (v) : a (e v)=b v := by
    have hv : joint p (e v).1*joint p (e v).2=joint p v.1*joint p v.2 := by
      unfold joint; simp only [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => by by_cases hi : i∈s <;> simp only [e,trades,Equiv.coe_fn_mk,hi,↓reduceIte]; exact mul_comm ..
    have hp : f (e v).1=f v.2 := Hf _ _ (fun i hi => show (if i∈s then _ else _) = _ from if_pos hi)
    have ht : g (e v).1=g v.1 := Hg _ _ (fun i hi => show (if i∈s then _ else _) = _ from if_neg fun h => disjoint_left.mp hu h hi)
    unfold a b; rw [hv,hp,ht]; ring
  have hl : ∑ v,a v= μ (f*g) := by
    change _= ∑ v, joint p v*(f v*g v)
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl; intro i _
    calc
       _ = (∑ v,joint p v)*(joint p i*(f i*g i)) := by rw [sum_mul];exact sum_congr rfl fun j _ => by dsimp only [a]; ring
       _ = _ := by rw [hs,one_mul]
  have hr : ∑ v,b v= μ f*μ g := by
    change _=(∑ i,joint p i*f i)*(∑ i,joint p i*g i)
    rw [Fintype.sum_prod_type,sum_mul_sum,sum_comm (f:=fun x y => b (x,y))]
  rw [← hl,← hr,← Equiv.sum_comp e]
  exact sum_congr rfl fun i _ => he i
end finite
end YM.RG02.Wick.Actor
