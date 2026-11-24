import YM.Integration.WilsonIndependentConditionedActualBudget

/-! A uniform polynomial invoice in the common clock, test radius, inverse clearance and amplitudes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedProfileCredit
open WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {ι:Type*}{v:ι→ℝ}

def Paid (v X:ι→ℝ):Prop:=∃P:Credit,∀i,1≤v i→|X i|≤P.buy (v i)

namespace Paid
variable {A B:ι→ℝ}

theorem fixed (v:ι→ℝ)(x:ℝ):Paid v (fun _=>x):=by
  refine ⟨⟨0,max 1 |x|,le_max_left ..⟩,fun _ _=>?_⟩
  simpa only [Credit.buy,pow_zero,mul_one] using le_max_right (1:ℝ) |x|

theorem direct (h:∀i,|A i|≤v i):Paid v A:=by
  exact ⟨⟨1,1,le_rfl⟩,fun i _=>by simpa only [Credit.buy,pow_one,one_mul] using h i⟩

theorem add (a:Paid v A)(b:Paid v B):Paid v (fun i=>A i+B i):=by
  obtain ⟨P,p⟩:=a
  obtain ⟨Q,q⟩:=b
  exact ⟨P.plus Q,fun i one=>(abs_add_le ..).trans ((add_le_add (p i one) (q i one)).trans (P.fuel Q one))⟩

theorem mul (a:Paid v A)(b:Paid v B):Paid v (fun i=>A i*B i):=by
  obtain ⟨P,p⟩:=a
  obtain ⟨Q,q⟩:=b
  refine ⟨P.prodC Q,fun i one=>?_⟩
  rw [Credit.products,abs_mul]
  exact mul_le_mul (p i one) (q i one) (abs_nonneg _) (zero_le_one.trans (P.purchase one))

theorem pow (a:Paid v A)(n:ℕ):Paid v (fun i=>A i^n):=by
  induction n with
  | zero=>simpa only [pow_zero] using fixed v 1
  | succ n ih=>simpa only [pow_succ] using ih.mul a

theorem abs (a:Paid v A):Paid v (fun i=>|A i|):=by simpa only [Paid,abs_abs] using a

theorem max (a:Paid v A)(b:Paid v B):Paid v (fun i=>Max.max (A i) (B i)):=by
  obtain ⟨P,p⟩:=a
  obtain ⟨Q,q⟩:=b
  refine ⟨P.plus Q,fun i one=>?_⟩
  rcases le_total (A i) (B i) with h|h
  · change |Max.max (A i) (B i)| ≤ _
    rw [max_eq_right h]
    exact (q i one).trans (Credit.thickened P one)
  · change |Max.max (A i) (B i)| ≤ _
    rw [max_eq_left h]
    exact (p i one).trans (Credit.thickens Q one)

theorem products {j:Type*}(s:Finset j)(F:j→ι→ℝ)(h:∀a,Paid v (F a)):
    Paid v (fun i=>∏a∈s,F a i):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa only [Finset.prod_empty] using fixed v 1
  | insert a s h' ih=>simpa only [Finset.prod_insert h'] using (h a).mul ih

theorem book (h:Paid v A)(C:Credit):Paid v (fun i=>C.buy (A i)):=
  (fixed v C.x).mul (h.pow C.d)

end Paid
end YM.Integration.WilsonIndependentConditionedProfileCredit
