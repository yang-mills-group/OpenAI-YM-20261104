import YM.RegulatorIR.Uniform.Stamps
import YM.RegulatorIR.Budget.Draft
import YM.RegulatorIR.Diagram.Heat

/-! Family-polynomial bounds on tensors. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Budget.Packet Diagram Budget.Layer Budget.Tuple
open scoped Topology ENNReal BigOperators Classical
variable {W:Type}{I J: W→Type}{r s : ℕ}

/-- absolute cost of a mark-indexed family -/
def Claim (L:Meter W) {A : (w:W)→ Tariff (I w)}(B:(w:W) → Premium (A w))(u: W → ℝ≥0∞)(T:(w:W) → Packet (I w) r): Prop := Carry L u fun w=>markQ (B w) (T w)
/-- translation-free cost -/
def Workday (L:Meter W)(A:(w:W) → Tariff (I w))(T:(w:W) → Packet (I w) r) : Prop:=∃ f:W → ℝ≥0∞, Poly L f ∧ ∀ w, localQ (A w) (T w) (f w)
/-- two-direction row costs -/
def Beam (L:Meter W)(A:(w:W) → Tariff (I w))(T:(w:W) → Layer (I w) (I w)):Prop:=∃ f : W→ℝ≥0∞, Poly L f ∧ ∀ w, row (T w) (A w) id id (f w) ∧ row (swap (T w)) (A w) id id (f w)

namespace Claim
variable {L:Meter W} {A : (w:W)→ Tariff (I w)}{B:(w:W)→Premium (A w)}{u:W→ℝ≥0∞}{T U:(w:W)→ Packet (I w) r}
lemma zeroQ : Claim L B u (fun w=>(0:Packet (I w) r)):= Carry.mono (Carry.zeroQ u) (fun _=> (quota_zero _).le)
lemma add (h:Claim L B u T)(hh:Claim L B u U): Claim L B u (fun w=> T w+U w) := Carry.mono (Carry.add h hh) fun _=>quota_add ..
lemma smul (h:Claim L B u T)(c: W→ℝ)(hh:Poly L fun w=>‖c w‖ₑ): Claim L B u (fun w=> c w • T w):= Carry.mono (Carry.mul_left hh h) (fun _=> (quota_times ..).le)
lemma csmul (h:Claim L B u T)(c:ℝ): Claim L B u (fun w=> c • T w) := Claim.smul h _ (Poly.standard _ (by finiteness))
lemma sub (h:Claim L B u T)(hh:Claim L B u U):Claim L B u (fun w=> T w-U w) := by simpa only [neg_one_smul, sub_eq_add_neg] using Claim.add h (Claim.csmul hh (-1))
lemma sum {Z:Type} (f:Z→(w:W)→Packet (I w) r)(s:Finset Z)(h:∀ i∈s,Claim L B u (f i)):Claim L B u (fun w=>∑ i∈s,f i w):= Carry.mono (Carry.sum _ (fun i w=> markQ (B w) (f i w)) h) fun _=>quota_sum ..
lemma robust (h:Claim L B u T):Claim L B u (fun w=>Packet.symmetry (T w)):= Carry.mono h fun _=>mark_symmetry
lemma cost (h:Claim L B u T) w (hp:u w≠⊤) : markQ (B w) (T w)≠⊤:= Carry.cost h w hp
lemma submits (h:Claim L B u T)(g:Poly L u): Workday L A T:= ⟨_,Carry.admit h g,fun w=>local_paid (B w) (T w)⟩
lemma draft_budget {K:(w:W)→Layer (I w) (I w)} (h:Claim L B u T)(hk: Beam L A K) : Claim L B u (fun w=>draft (K w) (T w)) := by
 obtain ⟨f,hf,hK⟩:=hk; exact Carry.mono (Carry.mul_right h (hf.powQ r)) (fun w=> mark_draft (hK w).2 _)
lemma knot_budget {K:(w:W)→Layer (I w) (I w)} {T:(w:W)→Packet (I w) (r+1)}{S:(w:W) → Packet (I w) (s+1)} (h:Claim L B u T)(hh:Workday L A S)(hk:Beam L A K): Claim L B u (fun w=> Packet.knot (K w) (T w) (S w)) := by
 obtain ⟨f,hf,H⟩:= hh; obtain ⟨g,hg,G⟩:= hk; exact Carry.mono (Carry.mul_right h (hf.mul hg)) fun w=>Packet.knot_mark _ (B w) (G w).1 (G w).2 (H w)
lemma knot_budget' {K:(w:W)→Layer (I w) (I w)} {T:(w:W)→Packet (I w) (r+1)}{S:(w:W)→Packet (I w) (s+1)}(h:Workday L A T)(hh:Claim L B u S)(hk:Beam L A K): Claim L B u (fun w=>Packet.knot (K w) (T w) (S w)) := by
 obtain ⟨f,hf,H⟩:=h; obtain ⟨g,hg,G⟩:= hk
 exact Carry.mono (Carry.mul_right (Carry.mul_right hh hg) hf) fun w=>Packet.knot_remnant _ (B w) (G w).2 (H w)
lemma loop_budget {K:(w:W)→Layer (I w) (I w)} {T:(w:W)→Packet (I w) (r+2)}(h:Claim L B u T)(hk:Beam L A K): Claim L B u (fun w=>Packet.loop (T w) (K w)) := by
 obtain ⟨g,hg,H⟩:=hk; exact Carry.mono (Carry.mul_left hg h) fun w=>Packet.loop_mark _ (row_to_sup (H w).1)
end Claim

namespace Workday
variable {L:Meter W} {A : (w:W)→ Tariff (I w)}{T U:(w:W)→ Packet (I w) r}
lemma zeroQ : Workday L A (fun w=>(0:Packet (I w) r)):=⟨0,Poly.zeroQ _,fun _=>local_zero _⟩
lemma add (h:Workday L A T)(hh:Workday L A U): Workday L A (fun w=> T w+U w) := by obtain ⟨f,h,H⟩:=h;obtain ⟨g,h',G⟩:=hh; exact ⟨_,h.add h',fun w=> local_add (H w) (G w)⟩
lemma smul (h:Workday L A T)(c: W→ℝ)(hh:Poly L fun w=>‖c w‖ₑ): Workday L A (fun w=> c w • T w):=by obtain ⟨f,h,H⟩:=h; exact ⟨_,hh.mul h,fun w=> local_gold (H w) _⟩
lemma csmul (h:Workday L A T)(c:ℝ): Workday L A (fun w=> c • T w) := Workday.smul h _ (Poly.standard _ (by finiteness))
lemma sum {Z:Type} (f:Z→(w:W)→Packet (I w) r)(s:Finset Z)(h:∀ i∈s,Workday L A (f i)):Workday L A (fun w=>∑ i∈s,f i w):=by
 induction s using Finset.induction_on with
 | empty=>simp; exact Workday.zeroQ
 | insert i s he ih=>simp_rw [Finset.sum_insert he]; exact Workday.add (h _ (Finset.mem_insert_self ..)) (ih fun _ hh=>h _ (Finset.mem_insert_of_mem hh))
lemma robust (h:Workday L A T):Workday L A (fun w=>Packet.symmetry (T w)):=by obtain ⟨f,h,H⟩:=h;exact ⟨_,h,fun w=> local_symmetry (H w)⟩
lemma draft_budget {K:(w:W)→Layer (I w) (I w)} (h:Workday L A T)(hk: Beam L A K) : Workday L A (fun w=>draft (K w) (T w)) := by
 obtain ⟨f,h,H⟩:=h; obtain ⟨g,hg,G⟩:=hk; exact ⟨_,h.mul (hg.powQ r),fun w=> local_draft (G w).1 (G w).2 (H w)⟩
lemma knot_budget {K:(w:W)→Layer (I w) (I w)} {T:(w:W)→Packet (I w) (r+1)}{S:(w:W) → Packet (I w) (s+1)} (h:Workday L A T)(hh:Workday L A S)(hk:Beam L A K): Workday L A (fun w=> Packet.knot (K w) (T w) (S w)) := by obtain ⟨f,h,H⟩:=h;obtain ⟨g,hg,G⟩:=hh;obtain ⟨k,hk,K⟩:=hk; exact ⟨_,h.mul (hg.mul hk),fun w=> Packet.knot_local (K w).1 (K w).2 (H w) (G w)⟩
lemma loop_budget {K:(w:W)→Layer (I w) (I w)} {T:(w:W)→Packet (I w) (r+2)}(h:Workday L A T)(hk:Beam L A K): Workday L A (fun w=>Packet.loop (T w) (K w)) := by
 obtain ⟨f,h,H⟩:=h;obtain ⟨g,hg,G⟩:=hk; exact ⟨_,hg.mul h,fun w=>Packet.loop_local (H w) (row_to_sup (G w).1)⟩
end Workday
end YM.RegulatorIR.Uniform
