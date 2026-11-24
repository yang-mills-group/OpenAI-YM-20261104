import YM.Comparison.RG02.Order.Pay
/-!
# Spur inputs, no imaginary part in *unmarked* entries

 Needed despite complex insertions (phase data on global vacuum remain separate). This lets us
 compare directly to the exponential of formal vacuum coefficients in the large torus if not
 estimating a single global Taylor price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Function Finset MeasureTheory
open Marker Multi Join
open YM.Comparison.RG02.Cumulants
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open scoped BigOperators Topology Classical
variable {V : Type} [DecidableEq V] {R : Census V} {r : ℕ} {X : Type*}

def Rim (z : ℂ) := ∃ t:ℝ, z=t
namespace Rim
lemma ofReal (x:ℝ) : Rim (x:ℂ) := ⟨x,rfl⟩
lemma natural (x :ℕ) : Rim (x:ℂ) := ⟨x,by rw [Complex.ofReal_natCast]⟩
theorem zero : Rim 0:=⟨0,by simp⟩
theorem one : Rim 1:=⟨1,by simp⟩
variable {x y :ℂ}
lemma re (h : Rim x) : Complex.ofReal x.re=x:=by obtain ⟨t,rfl⟩:=h; simp
lemma add (h : Rim x) (k : Rim y) : Rim (x+y) := by obtain ⟨t,rfl⟩:=h; obtain ⟨u,rfl⟩:=k; rw [← Complex.ofReal_add]; exact ofReal _
lemma mul (h : Rim x) (k : Rim y) : Rim (x*y) := by obtain ⟨t,rfl⟩:=h; obtain ⟨u,rfl⟩:=k; rw [← Complex.ofReal_mul]; exact ofReal _
lemma neg (h : Rim x) : Rim (-x):= by obtain ⟨t,rfl⟩:=h; rw [← Complex.ofReal_neg]; exact ofReal _
lemma inv (h : Rim x) : Rim x⁻¹:= by obtain ⟨t,rfl⟩:=h; rw [← Complex.ofReal_inv]; exact ofReal _
lemma pow (h : Rim x) (r : ℕ) : Rim (x^r):= by obtain ⟨t,rfl⟩:=h; rw [← Complex.ofReal_pow]; exact ofReal _
lemma sum (s : Finset X) {g:X→ℂ} (h : ∀ i∈s,Rim (g i)) : Rim (∑ i∈s,g i) := by
  induction s using Finset.induction with
  | empty=> rw [Finset.sum_empty]; exact zero
  | insert a s hi ih=> rw [Finset.sum_insert hi]; exact (h a (mem_insert_self ..)).add (ih fun i he=> h i (mem_insert_of_mem he))
lemma integrate [MeasurableSpace X] (μ:Measure X) {f:X→ℂ} (h : ∀ i,Rim (f i)) : Rim (∫ x,f x ∂μ) := by choose t ht using h; rw [funext ht]; exact ⟨_, integral_ofReal⟩
end Rim

namespace PolyRim

def Real (x : Poly R) := ∀ t,Rim (x.part t)
theorem one : Real (1:Poly R) := fun t=> by rw [Poly.one_part]; split_ifs; exact Rim.one; exact Rim.zero
lemma negate {x : Poly R} (h : Real x) : Real (-x) := fun t=> by rw [Poly.part_neg]; exact (h t).neg
lemma add {x y : Poly R} (h : Real x) (k : Real y) : Real (x+y) := fun t=> (h t).add (k t)
lemma multiply {x y : Poly R} (h : Real x) (k : Real y) : Real (x*y) := fun t=> by
  rw [Poly.part_mul]; exact Rim.sum _ (fun i _=>Rim.sum _ fun j _=> by split_ifs; exact (h i).mul (k j); exact Rim.zero)
lemma power {x : Poly R} (h : Real x) (n : ℕ) : Real (x^n) := by
  induction n with
  | zero=> rw [pow_zero]; exact one
  | succ n ih=> rw [pow_succ]; exact multiply ih h
lemma cumulants [Fintype V] (x : Poly R) (h : Real x) (he : x.part R.quiet=1) : Real (connected x) := by
    rw [log_formula he]; unfold unipotentLog; intro t
    rw [Poly.part_sum]; apply Rim.sum; intro i _; exact ((Rim.natural (i+1)).inv.neg).mul (power (show Real (1-x) from sub_eq_add_neg 1 x ▸ add one (negate h)) _ t)
end PolyRim

variable [Fintype V]
def Simple (x : Grade R r) := PolyRim.Real (Order.denominator x)
lemma real_entries (x : Grade R r) (h : ∀ t : Index r,Rim (x.part (Join.pair R.quiet t))) : Simple x := by
   intro t; unfold denominator; nth_rw 1 [← Join.pair_reunite t]; rw [bottom_value]; split; exact h _; exact Rim.zero
lemma at_value (x : Grade R r) (h : Simple x) (z : ℝ) : Rim ((value (z:ℂ) x).part R.quiet):=by
   rw [vpart]; apply Rim.sum; intro i hi
   refine ((Rim.ofReal z).pow i).mul ?_
   rw [observe,if_pos (show i≤r by simpa using hi)]
   change Rim ((i.factorial:ℂ)⁻¹*x.part _); apply (Rim.natural i.factorial).inv.mul
   have ht := h (Join.pair R.quiet (pick r i)); unfold denominator at ht; rwa [bottom_value,if_pos rfl] at ht
lemma log_color (x : Grade R r) (h : Simple x) (hu : UnitLeading x) : Simple (logVac x) := by
   unfold Simple Order.denominator; rw [log_vacant hu]; exact PolyRim.cumulants _ h ((bottom_quiet _).trans hu)
end YM.Comparison.RG02.Order
