import YM.AllOrder.Ink.Snug
import YM.AllOrder.Ink.Money
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
open Method
abbrev Bills (α:Type):= ∀ n:Side,rule α n→ℝ
variable {V:Type} (Ad:Side→Prop)(Λ:V→ℝ)
-- all comp constants paid post, c-polynomial
abbrev dearth (a:ℝ)(n:Side):= Real.exp (-a*n.val)
def Pert (Ad:Side→Prop) (A:Bills α) (U:Field α)(a:ℝ) (C:ℝ) (D:Side→ℝ)(k:ℕ) := U.Good a C k ∧ ∀ n:Side,Ad n → Prices k (D n * dearth a n) (A n-U.table n)
-- include `[autoImplicit false]` concerns
variable {Ad Λ} {A B: Bills α}{U:Field α}{D':Side→ℝ}
lemma Pert.le (h:Pert Ad A U a C D' k)(hl:a≥b)(hq:k≤N) {V:Side→ℝ}{X:ℝ}(hv:D' ≤ V)(hC:C≤X)(hp:∀ n,0≤V n): Pert Ad A U b X V N := by
   refine ⟨h.1.debt hl hC hq,fun n hn=> price_mono (Prices.up hq (h.2 n hn)) ?_⟩; exact mul_le_mul (hv _) (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hl) (by positivity))) (Real.exp_pos _).le (hp n)
def grant {V:Type}(Ad: Side→Prop)(Λ:V→ℝ) (A:V→Bills α)(a:ℝ)(k:ℕ): Prop := ∃ (F:V→Field α) (C:V→ℝ)(D:V→Side→ℝ), Grade Λ C ∧ Pay Λ D ∧ ∀ v,Pert Ad (A v) (F v) a (C v) (D v) k
def Apt {V:Type}(Ad:Side→Prop)(Λ:V→ℝ)(A: V→ Bills α)(k:ℕ):Prop:= ∃ a,0<a∧ grant Ad Λ A a k
namespace Apt
variable {A B:V→ Bills α}
lemma squeeze (h:grant Ad Λ A a k)(he:b≤a) (hl:k≤N): grant Ad Λ A b N := by obtain ⟨F,C,D,hC,hD,h'⟩:=h; exact ⟨F,C,D,hC,hD,fun v=>(h' v).le he hl le_rfl le_rfl (hD.nonneg v)⟩
lemma grow (h:Apt Ad Λ A k)(hp:k≤N):Apt Ad Λ A N := by obtain ⟨a,h,h'⟩:=h; exact ⟨a,h,squeeze h' le_rfl hp⟩
lemma pure (a:ℝ)(F:V→Field α) (C:V→ℝ)(ha:0<a)(hC:Grade Λ C)(h:∀v,(F v).Good a (C v) k)(he:∀v n, Ad n→ A v n= (F v).table n):Apt Ad Λ A k:= by
 refine ⟨a,ha,F,C,(fun _ _=>0),hC,Pay.fixed Λ _ le_rfl,fun v=>⟨h v,fun n hn=>?_⟩⟩
 rw [he v n hn,sub_self,zero_mul]; exact price_const (show |(0:ℝ)| ≤0 from (abs_zero).le) _
lemma adapt (h:Apt Ad Λ A k)(he:∀v n,Ad n→A v n=B v n): Apt Ad Λ B k:= by obtain ⟨a,ha,F,C,D,hC,hD,h⟩:=h; exact ⟨a,ha,F,C,D,hC,hD,fun v=> ⟨(h v).1,fun n hn=> he v n hn ▸ (h v).2 n hn⟩⟩
lemma null (Λ:V→ℝ):Apt Ad Λ (fun (_:V) _ (_:rule α _)=>0) k:= by refine pure 1 (fun v=>Field.void α) (fun _=>0) zero_lt_one (gia _ le_rfl) (fun i=>Field.silent) (fun v n hn=>?_); exact (Field.dormant ..).symm
lemma scaleG (h:Apt Ad Λ A k)(t:V→ℝ)(ht:Grade Λ fun v=> |t v|) : Apt Ad Λ (fun v n=> t v • A v n) k:= by
   obtain ⟨a,ha,F,C,D,hC,hD,h⟩:= h; let Z(v:V):Field α:= Field.scale (F v) (t v); refine ⟨a,ha,Z,_,_,ht.mul hC,(Pay.lift ht).times hD,fun v=>⟨Field.scale_good _ ((h v).1) (t v),fun n hn=>?_⟩⟩; rw [show (Z v).table n= _ from Field.scale_table (F v) (t v) n, ← smul_sub, mul_assoc]; exact price_scale ((h v).2 n hn) (t v)
lemma scale (h:Apt Ad Λ A k)(a:ℝ): Apt Ad Λ (fun v n=>a• A v n) k:= h.scaleG (fun _=>a) (gia _ (abs_nonneg a))
lemma add (h:Apt Ad Λ A k)(H:Apt Ad Λ B k): Apt Ad Λ (fun v n=>A v n+B v n) k:= by
 obtain ⟨a,h0,h'⟩:=h; obtain ⟨b,hB,H⟩:= H; let t:=min a b; have hp:0<t:=lt_min h0 hB
 obtain ⟨F,C,D,hC,hD,h⟩:= squeeze h' (min_le_left a b) (le_refl k)
 obtain ⟨Z,C',D',hc,hd,H⟩:= squeeze H (min_le_right a b) (le_refl k); let R(v:V)(i:Fin 2): Field α:= Fin.cases (F v) (fun _=>Z v) i; let W(v:V): Fin 2→ℝ:= ![C v,C' v];
 have hr(v i): (R v i).Good t (W v i) k:= by fin_cases i; exact (h v).1; exact (H v).1
 have hR(v:V):SumBudget (W v) (C v+C' v) := budget_finite (fun i=>(hr v i).nonneg) (show (∑ i:Fin 2, W v i) ≤ _ by simp [W,Fin.sum_univ_two]); let L v:= Field.sum (R v)
 refine ⟨t,hp,L,_,_,hC.add hc,Pay.stamp hD hd,fun v=>⟨Field.keep _ (hr v) (hR v),fun n hn=> ?_⟩⟩; rw [show (L v).table n= _ from (Field.contribution _ (hr v) (hR v) hp.le n), Fin.sum_univ_two, show A v n+B v n-_= (A v n-(F v).table n)+(B v n-(Z v).table n) from ?_, add_mul]; · exact price_add ((h v).2 n hn) ((H v).2 n hn)
 change _ - ((F v).table n+(Z v).table n)=_; abel
lemma pile {ι:Type*}(s: Finset ι)(F:ι →V→Bills α)(h:∀ i∈s,Apt Ad Λ (F i) k): Apt Ad Λ (fun v n=>∑ i∈s,F i v n) k:= by induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact Apt.null _
 | insert i s hi ih=> simp_rw [sum_insert hi]; exact Apt.add (h i (mem_insert_self ..)) (ih (fun j hj=>h j (mem_insert_of_mem hj)))
end Apt
end Money
end YM.AllOrder.Ink
