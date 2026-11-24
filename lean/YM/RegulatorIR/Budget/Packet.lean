import YM.RegulatorIR.Budget.Deck
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Pack homogeneous degree-r fields in log links with no r! in evaluation.
Use symmetric kernel after contraction (unsymmetrized intermediate estimates
can hold arbitrary leg). Bulk tensors read modulo extensive pure vacuum;
marked sources track scalars.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget

open Set Function
open scoped ENNReal NNReal Topology BigOperators Classical

abbrev Tuple (I : Type) (r:ℕ):= Fin r→I
abbrev Packet (I : Type) (r:ℕ):= Tuple I r → ℝ

namespace Tuple
variable {X Y : Type} {r s : ℕ}
def glueEquiv (X:Type) (r:ℕ) : X × Tuple X r ≃ Tuple X (r+1):= Fin.consEquiv (fun _=>X)
def cutLeft (u:Tuple X (r+s)): Tuple X r := fun i=> u (Fin.castAdd s i)
def cutRight (u:Tuple X (r+s)): Tuple X s:=fun i=> u (Fin.natAdd r i)
@[simp] lemma cutleft (u:Tuple X r)(v:Tuple X s): cutLeft (Fin.append u v)=u:= funext fun _=> Fin.append_left ..
@[simp] lemma cutright (u:Tuple X r)(v:Tuple X s): cutRight (Fin.append u v)=v:=funext fun _=>Fin.append_right ..
lemma recombine (u:Tuple X (r+s)): Fin.append (cutLeft (r:=r) u) (cutRight (r:=r) u) = u := by
  funext i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Fin.append_left]; rfl
  rw [Fin.append_right]; rfl
@[simp] lemma comp_append (f:X→Y)(u:Tuple X r)(v:Tuple X s): f ∘ Fin.append u v=Fin.append (f ∘ u) (f ∘ v):=(recombine _).symm.trans (congr_arg₂ Fin.append (by
    show cutLeft (f ∘ Fin.append u v)= f∘u; funext i; simp [cutLeft]) (by
    show cutRight (f∘Fin.append u v)=f∘v; funext i; simp [cutRight]))
lemma comp_cons (f:X→Y)(u)(v:Tuple X r):f ∘ Fin.cons u v=Fin.cons (f u) (f∘v):=by
  funext i; exact Fin.cases rfl (fun j=>by simp) i

abbrev Hold (i:Fin r)(x:X) := Stalk (fun z:Tuple X r=> z i) x

/-- permute slots by composition -/
def perm (X:Type)(e:Equiv.Perm (Fin r)):Equiv.Perm (Tuple X r) where
 toFun x:=x∘e
 invFun x:=x∘e.symm
 left_inv x:=by simp [Function.comp_assoc]
 right_inv x:=by simp [Function.comp_assoc]

def heldPerm (e:Equiv.Perm (Fin r))(i:Fin r)(x:X): Hold (e i) x≃ Hold i x:=
 Equiv.subtypeEquiv (perm X e) fun _=>Iff.rfl
-- Winding all positions similarly

def winding (e:X≃Y)(r : ℕ) : Tuple X r≃Tuple Y r where
 toFun x:=e∘x
 invFun x:=e.symm ∘ x
 left_inv x:=by ext; simp
 right_inv x:=by ext; simp
end Tuple

namespace Packet
open Tuple
variable {X Y : Type} {r : ℕ}
def IsSym (T:Packet X r):Prop:= ∀ (e:Equiv.Perm (Fin r)) z,T (z ∘ e)=T z

def symmetry (T:Packet X r):Packet X r:=
  (Fintype.card (Equiv.Perm (Fin r)) : ℝ)⁻¹ • ∑ e:Equiv.Perm (Fin r), (T ∘ ⇑(perm X e))
lemma symmetry_at (T:Packet X r) z : symmetry T z=(Fintype.card (Equiv.Perm (Fin r)) : ℝ)⁻¹ * ∑ e:Equiv.Perm (Fin r), T (z ∘ e) := by simp [symmetry,Finset.sum_apply]; rfl
lemma is_symmetry (T:Packet X r): IsSym (symmetry T) := by
 intro p x
 rw [symmetry_at,symmetry_at]; apply congr_arg
 change ∑ i:Equiv.Perm (Fin r), T ((x ∘ p) ∘ i)=_
 have h (i:Equiv.Perm (Fin r)): (x ∘ p) ∘ i=x ∘ (p*i):=rfl
 simp_rw [h]
 exact Equiv.sum_comp (Equiv.mulLeft p) (fun i=> T (x ∘ i))
lemma symmetric_already (T:Packet X r)(h:IsSym T):symmetry T=T:=by
 ext z
 unfold IsSym at h; rw [symmetry_at]; simp_rw [h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp

/-- Costs holding an arbitrary single leg fixed. The nonabsolute (signed)
kernel is converted to absolute values before summing. -/
def localQ (A:Tariff X)(T:Packet X r)(c:ℝ≥0∞):Prop:=
 ∀ (i:Fin r) (x:X), Stalk.scopeQ (fun p:Tuple X r=>p i) T A.diameter x ≤ c

def markQ {A:Tariff X}(B: Premium A)(T:Packet X r):ℝ≥0∞:= quota T B.width
lemma local_mono (A:Tariff X){T:Packet X r}{b c:ℝ≥0∞} (h:localQ A T b)(hh:b≤c):localQ A T c := fun i x=> (h i x).trans hh
lemma local_paid {A:Tariff X}(B: Premium A)(T:Packet X r):localQ A T (markQ B T):=fun _ _=> (Stalk.over_le ..).trans (quota_mono T (fun _=> B.width_diameter _))
lemma anchor_swap {T:Packet X r} (A:Tariff X)(i: Fin r)(e:Equiv.Perm (Fin r))(x:X):
    Stalk.scopeQ (fun p:Tuple X r=>p i) (T ∘ ⇑(perm X e)) A.diameter x = Stalk.scopeQ (fun p:Tuple X r=>p (e.symm i)) T A.diameter x := by
   let f := Equiv.subtypeEquiv (p:=fun u:Tuple X r=>u i=x) (q:=fun u:Tuple X r=> u (e.symm i)=x) (Tuple.perm X e) (by intro z; change z i=x ↔ z (e (e.symm i))=x; rw [e.apply_symm_apply])
   unfold Stalk.scopeQ quota
   rw [← f.tsum_eq (fun w=> ‖T w.val‖ₑ*A.diameter w.val)]; apply tsum_congr;intro b; change _ = _*A.diameter (b.val ∘ e); rw [A.diameter_perm]; rfl
lemma local_anchor {T:Packet X r}(A:Tariff X)(i:Fin r){c:ℝ≥0∞}(h:IsSym T)(hh:∀ x, Stalk.scopeQ (fun p:Tuple X r=>p i) T A.diameter x≤c):localQ A T c:= by
 intro j x
 let e:=Equiv.swap j i
 have he : T=T ∘ ⇑(Tuple.perm X e):=funext fun z=> (h e z).symm
 rw [he,anchor_swap,show e.symm j=i by simp [e]]; exact hh _
lemma local_version {T:Packet X r}(A:Tariff X)(e:Equiv.Perm (Fin r)){c:ℝ≥0∞}(h:localQ A T c):localQ A (T ∘ ⇑(Tuple.perm X e)) c:=by
 intro i x; rw [anchor_swap]; apply h
lemma slot_moment {T:Packet X r}{A:Tariff X}{B:Premium A}(e:Equiv.Perm (Fin r)) : markQ B (T ∘ ⇑(Tuple.perm X e))=markQ B T:= by
 unfold markQ
 convert quota_perm (Tuple.perm X e) T B.width using 2
 ext1 x; exact (B.width_perm x e).symm
lemma local_add {T W:Packet X r}{A:Tariff X}{a b:ℝ≥0∞}(h:localQ A T a)(hw:localQ A W b) : localQ A (T+W) (a+b) := fun i x=>
 (quota_add (T ∘ (Subtype.val : Hold i x→_)) (W ∘ Subtype.val) _).trans (add_le_add (h ..) (hw ..))
lemma local_gold {T:Packet X r}{A:Tariff X}{a:ℝ≥0∞}(h:localQ A T a)(u:ℝ):localQ A (u • T) (‖u‖ₑ*a):=fun i x=> (quota_times (T ∘ (Subtype.val : Hold i x→_)) (fun z=>A.diameter z.val) u).trans_le (mul_le_mul_right (h i x) _)
lemma local_zero {A:Tariff X} (c:ℝ≥0∞) : localQ A (0:Packet X r) c:= fun _ _=>le_trans (quota_zero _).le bot_le
lemma local_sum {I:Type} (s:Finset I)(f:I→Packet X r)(g:I→ℝ≥0∞) {A:Tariff X} (h:∀ i∈s,localQ A (f i) (g i)):localQ A (∑ i∈s,f i) (∑ i∈s,g i):=by
 induction s using Finset.induction_on with
 | empty=>simp; exact local_zero _
 | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact local_add (h i (Finset.mem_insert_self ..)) (ih fun _ h' => h _ (Finset.mem_insert_of_mem h'))

private lemma paid_div (b:ℝ≥0∞) (α:Type)[Fintype α][Nonempty α]:
    ‖((Fintype.card α:ℝ)⁻¹)‖ₑ * ∑ _:α,b=b := by
 have ht : ‖((Fintype.card α:ℝ)⁻¹)‖ₑ = (Fintype.card α:ℝ≥0∞)⁻¹ := by
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity),ENNReal.ofReal_inv_of_pos (by positivity)]; simp
 simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_pos.ne') (by finiteness),one_mul]

lemma local_symmetry {T:Packet X r}{A:Tariff X}{c:ℝ≥0∞}(h:localQ A T c): localQ A (symmetry T) c :=
 local_mono A (local_gold (local_sum Finset.univ _ (fun _=>c) (fun e _=>local_version _ e h)) _) (paid_div ..).le
lemma mark_symmetry {T:Packet X r}{A:Tariff X}{B:Premium A} : markQ B (symmetry T)≤markQ B T := by
 unfold markQ
 let a:= (Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹
 apply (quota_times (∑ e:Equiv.Perm (Fin r), T ∘ ⇑(perm X e)) B.width a).trans_le
 have hs:= quota_sum (Finset.univ (α:=Equiv.Perm (Fin r))) (fun e=>T ∘ ⇑(perm X e)) B.width
 exact (mul_le_mul_right hs ‖a‖ₑ).trans_eq (by simp_rw [show ∀ e:Equiv.Perm (Fin r),quota (T ∘ ⇑(Tuple.perm X e)) B.width=quota T B.width from fun e=>slot_moment e]; exact paid_div ..)
end Packet
end YM.RegulatorIR.Budget
