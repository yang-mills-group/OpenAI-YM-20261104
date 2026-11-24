import YM.Pert.First.Guests
/-! Concrete orthonormal self/anti-self-dual two-form bases (normalization on positive pairs, not ordered pairs). Orientation `(0,1,2,3)`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open scoped Topology Classical BigOperators
local notation "I3" => Fin 3

def partner (i : I3) : Axis × Axis := i.cases (2,3) (fun j => j.cases (3,1) (fun _=>(1,2)))
def ternaryAxis (i : I3) : Axis := i.cases 1 (fun j=> j.cases 2 (fun _ => 3))
def signRight (h : Bool): ℤ := if h=true then 1 else -1
def antisite (u : Axis × Axis) (a b : Axis) : ℤ := if (a,b)=u then 1 else if (b,a)=u then -1 else 0
def fanI (h : Bool) (i : I3) (a b : Axis) := antisite (0,ternaryAxis i) a b + signRight h * antisite (partner i) a b
def fan (h : Bool) (i : I3) (a b : Axis) := (fanI h i a b:ℝ) / Real.sqrt 2
def eps3 (i j k : I3) : ℤ := if j = i+1 ∧ k=i+2 then 1 else if j=i+2∧k=i+1 then -1 else 0

section finite_receipts
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [-instance] Classical.propDecidable
/-- Pure integer matrix rule; same oriented signs used at curvature slots. -/
lemma fan_anticommute_int : ∀ h i j a b, (∑ e, fanI h i a e * fanI h j b e) + (∑ e, fanI h j a e * fanI h i b e) = if i=j∧a=b then 2 else 0 := by decide
lemma fan_ortho_int : ∀ h h' i j, (∑a : Axis,∑ b : Axis, if a<b then fanI h i a b * fanI h' j a b else 0) = if h=h'∧i=j then 2 else 0 := by decide
lemma fan_antisymmetric_int : ∀ h i a b, fanI h i a b = -(fanI h i b a) := by decide
lemma orientations : ∀ h : Bool, signRight h * signRight h = 1 := by decide
lemma eps_swap12 : ∀ i j k, eps3 j i k = -eps3 i j k := by decide
lemma eps_swap23 : ∀ i j k, eps3 i k j = -eps3 i j k := by decide
end finite_receipts
lemma fan_flip (h : Bool) (i a b) : fan h i b a = -fan h i a b := by rw [fan, fan,fan_antisymmetric_int h i b a,Int.cast_neg,neg_div]
private theorem rooted (h i j a b) :
    ∑ e, fan h i a e * fan h j b e = (Real.sqrt 2*Real.sqrt 2)⁻¹ * ((∑ e, fanI h i a e * fanI h j b e : ℤ):ℝ) := by
  rw [Int.cast_sum,Finset.mul_sum]; apply Finset.sum_congr rfl
  intro e _; rw [Int.cast_mul,fan,fan,div_mul_div_comm, div_eq_mul_inv, mul_comm]
lemma sqrt_two_rule : Real.sqrt 2*Real.sqrt 2=2 := by rw [Real.mul_self_sqrt (by norm_num)]
lemma fan_anticommute (h i j a b) : (∑ e, fan h i a e * fan h j b e) + (∑ e, fan h j a e * fan h i b e) = if i=j ∧ a=b then 1 else 0 := by
  rw [rooted,rooted,sqrt_two_rule,←mul_add, ← Int.cast_add,fan_anticommute_int]
  by_cases h : i=j∧a=b <;> norm_num [h]
end YM.Pert.Triangle
