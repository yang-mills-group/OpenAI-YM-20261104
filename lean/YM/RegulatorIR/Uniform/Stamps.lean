import YM.RegulatorIR.Budget.Sums

/-! Uniform positive bounds in user-visible form (power polynomial, optional
single billing factor). A `Meter` only records the realized structural
number; it of course supplies no bounds on primitive data. The index family
is arbitrary so quantitative theorems may be consumed on concrete admissible
families. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W X : Type}

structure Meter (W : Type) where
 val : W→ℝ≥0∞
 above w : 1≤ val w
 below w : val w≠⊤

-- general proof arithmetic; polynomial constant displayed at the end
variable (L : Meter W) {f g v : W→ℝ≥0∞}

def Poly (L:Meter W)(f : W→ℝ≥0∞) := ∃ (C:ℝ≥0∞) (p : ℕ), C≠⊤ ∧ ∀ w,f w≤C * (L.val w)^p

namespace Poly
variable {L:Meter W}
lemma mono (h : Poly L g)(hh:f≤g): Poly L f:=by obtain ⟨c,p,hc,H⟩:=h; exact ⟨c,p,hc,fun w=>(hh w).trans (H w)⟩
lemma standard (L:Meter W){u : ℝ≥0∞}(h:u≠⊤) : Poly L (fun _=>u) := ⟨u,0,h,fun _=>by simp⟩
lemma zeroQ (L:Meter W) : Poly L 0 := standard L (u:=0) ENNReal.zero_ne_top
lemma oneQ (L:Meter W) : Poly L 1 := standard L ENNReal.one_ne_top
lemma roof (L:Meter W) : Poly L L.val:= ⟨1,1,(by finiteness),fun i=>by simp⟩
lemma add (h:Poly L f)(hh:Poly L g): Poly L (fun i=> f i+g i):=by
 obtain ⟨c,p,hc,H⟩:=h; obtain ⟨d,q,hd,G⟩:=hh;refine ⟨c+d,p+q,by finiteness,fun w=>?_⟩
 apply (add_le_add (H w) (G w)).trans; rw [add_mul]; exact add_le_add (mul_le_mul_right (pow_le_pow_right' (L.above ..) (by omega)) c) (mul_le_mul_right (pow_le_pow_right' (L.above ..) (by omega)) d)
lemma mul (h:Poly L f)(hh:Poly L g): Poly L (fun i=> f i*g i):=by
 obtain ⟨c,p,hc,H⟩:=h;obtain ⟨d,q,hd,G⟩:=hh;refine ⟨c*d,p+q,by finiteness,fun w=>?_⟩
 apply (mul_le_mul' (H w) (G w)).trans_eq; rw [pow_add]; ac_rfl
lemma powQ (h:Poly L f)(p:ℕ) : Poly L (fun i=>f i^p):= by induction p with
 | zero=> simpa using! (standard L ENNReal.one_ne_top)
 | succ p ih=> simpa only [pow_succ] using! ih.mul h
lemma sum (s: Finset X)(f:X→W→ℝ≥0∞)(h:∀ i∈s,Poly L (f i)):Poly L (fun i=>∑ j∈s,f j i):=by
 induction s using Finset.induction_on with
 | empty=> simpa using! (standard L ENNReal.zero_ne_top)
 | insert i s he ih=>simpa only [Finset.sum_insert he] using! (h i (Finset.mem_insert_self ..)).add (ih fun v hv=>h v (Finset.mem_insert_of_mem hv))
lemma cost (h:Poly L f) w : f w≠ ⊤ := by obtain ⟨c,p,hc,H⟩:=h; exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (ENNReal.pow_ne_top (L.below _))) (H w)
end Poly

/-- Single relative insertion budget; can absorb a fixed polynomial in L. -/
def Carry (L:Meter W) (v f : W → ℝ≥0∞) := ∃ f': W→ℝ≥0∞,Poly L f' ∧ ∀ w, f w ≤ f' w * v w
namespace Carry
variable {L : Meter W}
lemma mono (h : Carry L v g)(hh:f≤g): Carry L v f:=by obtain ⟨c,hc,H⟩:=h; exact ⟨c,hc,fun w=>(hh w).trans (H w)⟩
lemma zeroQ (v): Carry L v 0:=⟨0,Poly.zeroQ L,fun _=>by simp⟩
lemma unit (L:Meter W)(v):Carry L v v:=⟨1,Poly.oneQ L,by simp⟩
lemma add (h:Carry L v f)(hh:Carry L v g): Carry L v (fun i=> f i+g i):=by
 obtain ⟨c,hc,H⟩:=h;obtain ⟨d,hd,G⟩:=hh;exact ⟨_,hc.add hd,fun i=> (add_le_add (H i) (G i)).trans_eq (add_mul (c i) (d i) _).symm⟩
lemma sum (s: Finset X)(f:X→W→ℝ≥0∞)(h:∀ i∈s,Carry L v (f i)):Carry L v (fun i=>∑ j∈s,f j i):=by
 induction s using Finset.induction_on with
 | empty=> simpa using! (show Carry L v (fun _=>0) from zeroQ v)
 | insert i s he ih=>simpa only [Finset.sum_insert he] using! (h i (Finset.mem_insert_self ..)).add (ih fun q hv=>h q (Finset.mem_insert_of_mem hv))
lemma mul_right (h:Carry L v f)(hh:Poly L g): Carry L v (fun i=> f i*g i):=by
 obtain ⟨c,hc,H⟩:=h;exact ⟨_,hc.mul hh,fun w=> (mul_le_mul_left (H w) _).trans_eq (by ac_rfl)⟩
lemma mul_left (h:Poly L f)(hh:Carry L v g):Carry L v (fun i=> f i*g i) :=by simpa only [mul_comm] using hh.mul_right h
lemma charge {v' : W→ℝ≥0∞} (h: Carry L v f)(hh : Carry L v' v): Carry L v' f := by obtain ⟨a,ha,G⟩:= h; exact (mul_left ha hh).mono G
lemma cost (h:Carry L v f)(w)(hh:v w≠⊤):f w ≠ ⊤:=by obtain ⟨a,ha,h⟩:=h; exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ha.cost w) hh) (h w)
lemma scale {w : W→ℝ≥0∞} (h:Carry L v f): Carry L (fun i=> v i*w i) (fun i=>f i*w i):= by obtain ⟨c,hc,H⟩:=h; exact ⟨c,hc,fun i=> (mul_le_mul_left (H i) (w i)).trans_eq (mul_assoc ..)⟩
lemma admit (h:Carry L v f)(hv: Poly L v):Poly L f:=by obtain ⟨g,hg,H⟩:=h; exact (hg.mul hv).mono H
lemma regular (h:Poly L f):Carry L 1 f:= ⟨f,h,fun w=> by simp⟩
end Carry
end YM.RegulatorIR.Uniform
