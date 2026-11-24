import YM.Integration.WilsonOriginalPointPush

/-! Complex point evaluations act on the original square-free coefficient algebra with exact occupied-slot products. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointDilation
open Function Finset MeasureTheory Marker
open scoped Classical BigOperators Topology
variable {V : Type*} [DecidableEq V] {Γ : Census V} (z : V→ℂ)

def weight (s : Γ.Mode) : ℂ := ∏i∈s.val,z i

def act : Poly Γ→L[ℂ]Poly Γ := ContinuousLinearMap.pi fun s : Γ.Mode=>weight z s • Poly.get s

theorem part (p : Poly Γ) (s : Γ.Mode) : (act z p).part s=weight z s*p.part s := rfl

@[simp] theorem quiet : weight z Γ.quiet=1 := by change ∏i∈(∅ : Finset V),z i=1;simp

@[simp] theorem fire (v : V) : weight z (Γ.fire v)=z v := by change ∏i∈({v} : Finset V),z i=z v;simp

theorem send (k : Γ.Mode) (q : ℂ) : act z (Poly.send k q)=Poly.send k (weight z k*q) := by
  funext s
  change (act z (Poly.send k q)).part s=(Poly.send k (weight z k*q)).part s
  rw [part,Poly.part_send,Poly.part_send]
  split_ifs with h
  · rw [h]
  · exact mul_zero _

theorem one : act z (1:Poly Γ)=1 := by rw [show (1:Poly Γ)=Poly.send Γ.quiet 1 by rfl,send,quiet,one_mul]

theorem multiply (p q : Poly Γ) : act z (p*q)=act z p*act z q := by
  funext s
  change (act z (p*q)).part s=(act z p*act z q).part s
  simp only [part,Poly.part_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · have w : weight z s=weight z i*weight z j := by unfold weight;rw [←h.2,Finset.prod_union h.1]
    rw [w];ring
  · exact mul_zero _

theorem power (p : Poly Γ) (n : ℕ) : act z (p^n)=(act z p)^n := by
  induction n with
  | zero => simpa only [pow_zero] using one (Γ:=Γ) z
  | succ n ih => rw [pow_succ,multiply,ih,←pow_succ]

theorem product {ι : Type*} (s : Finset ι) (f : ι→Poly Γ) : act z (∏ i∈s,f i)=∏ i∈s,act z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one (Γ:=Γ) z
  | insert a t h ih => rw [Finset.prod_insert h,Finset.prod_insert h,multiply,ih]

theorem passed [Fintype V] (p : Poly Γ) : act z (Poly.pass p)=Poly.pass (act z p) := by simp only [Poly.pass,map_sum,map_smul,power]

end YM.Integration.WilsonOriginalPointDilation
