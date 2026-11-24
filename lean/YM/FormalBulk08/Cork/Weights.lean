import YM.FormalBulk08.Cork.Gym

/-! Reader kinetic jet unit reduction to sheet metric right at zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {A σ : ℝ}

lemma covana (f: Cover→ℝ)(p i) : (∑' v,cobound 1 p i v * f v)=∑ l:Axis,left ℝ 1 l p i*(f (step l)-f 0):= by
   rw [tsum_eq_sum (s:=Exterior.support) (fun b hb=> by rw [certified _ _ _ _ hb,zero_mul])]; simp_rw [cobound,Finset.sum_mul]; rw [Finset.sum_comm];refine Finset.sum_congr rfl fun l _=>?_; simp [mul_sub, sub_mul,mul_ite,ite_mul, Exterior.support,show ∃ x,step x=(step l:Cover) from ⟨l,rfl⟩]
lemma converted (f: Cover→ℝ)(p i) : (∑' v,cobound 1 p i (-v)* f v)=∑ l:Axis,left ℝ 1 l p i*(f (-step l)-f 0):= by
   rw [←Equiv.tsum_eq (Equiv.neg Cover)];simp only [Equiv.neg_apply,neg_neg]; have H:= covana (fun v=> f (-v)) p i; simpa only [neg_zero] using H
lemma shadowed (G : Cover→ℝ)(p i)(v): routed id G (fun _=>cobound 1 p i) v=∑ k: Axis,left ℝ 1 k p i * (G (v-step k)- G v) := by
   rw [routed,← Equiv.tsum_eq (Equiv.subLeft v)]; simp only [Equiv.subLeft_apply,id_eq,sub_sub_cancel]; simpa only [sub_zero,mul_comm] using covana (fun x=> G (v-x)) p i
lemma brought (G : Cover→ℝ)(p i)(v): routed id (transRows (cobound 1) i p) (fun _=> G) v=∑ k:Axis, left ℝ 1 k p i*(G (v+step k)- G v) := by rw [routed]; simpa only [sub_zero,id_eq,transRows,sub_neg_eq_add] using converted (fun x=> G (v-x)) p i

lemma pay_pivot (R f : Cover→ℝ)(H : Width σ A R)(hp : Pad f)(hs : 0<σ): Summable (fun v=> R v*f v) := by
   obtain ⟨N,C,hc,hC⟩:=hp; obtain ⟨B,hB,h⟩:=pockets N hs
   have he (v) : ‖R v*f v‖ ≤ (C*B)*(Real.exp (σ*size v)*‖R v‖) := by
       rw [norm_mul]; apply le_trans (mul_le_mul_of_nonneg_left ((hC v).trans (mul_le_mul_of_nonneg_left (h _ (by positivity)) hc)) (norm_nonneg _)); apply le_of_eq; ring
   exact Summable.of_norm_bounded (H.2.1.mul_left (C*B)) he

def scales (P : Cover →ℝ) (f:Cover→ℝ):= ∑' v,P v*f v
variable {I : Type*} {R f : Cover→ℝ}
lemma creeps (H : Width σ A R)(hp : Pad f)(hs:0<σ) (w:Cover): Summable (fun v=> R (v-w)*f v) := (Equiv.summable_iff (Equiv.addRight w)).mp ((pay_pivot R _ H (hp.shift w) hs).congr (fun v=> by simp))
lemma scales_minus (H: Width σ A R)(hp:Pad f)(hs : 0<σ) (w:Cover): scales (fun v=>R (v-w)-R v) f=scales R (fun v=> f (v+w)-f v):= by
   unfold scales; simp_rw [sub_mul,mul_sub]; rw [(creeps H hp hs w).tsum_sub (pay_pivot _ _ H hp hs),(pay_pivot R _ H (hp.shift w) hs).tsum_sub (pay_pivot _ f H hp hs)];congr 1; rw [←Equiv.tsum_eq (Equiv.addRight w)];simp

lemma click (L : I→ Cover)(c : I →ℝ)[Fintype I](H : Width σ A R)(hp : Pad f)(hs : 0<σ) : scales (fun v=>∑ i,c i*(R (v-L i)-R v)) f=∑ i,c i*scales R (fun v=> f (v+L i)-f v) := by
   simp_rw [← scales_minus H hp hs, scales, Finset.sum_mul]; rw [Summable.tsum_finsetSum]; swap
   · intro i _; have h:=((creeps H hp hs (L i)).sub (pay_pivot _ f H hp hs)).mul_left (c i); simpa only [mul_assoc, sub_mul] using! h
   refine Finset.sum_congr rfl fun i _=> ?_; rw [←tsum_mul_left]; simp_rw [mul_assoc]
lemma cash_X {Q : Row I (TypeFace 2)} (H : Q.strip σ A)(hs : 0<σ) (hp : Pad f)(i j): scales (composeRows Q (cobound 1) i j) f= ∑ b : TypeFace 2, ∑ k: Axis,left ℝ 1 k b j * scales (Q i b) (frow f k):= by
    obtain ⟨E,hE,h⟩:=Next.Free.delta_budget 1 σ
    unfold scales; simp_rw [composeRows,Finset.sum_mul]; rw [Summable.tsum_finsetSum]; swap
    · intro t _; exact pay_pivot _ f (width_routed hs.le (fun _=>le_rfl) (H _ t) (fun _=> h _ j)) hp hs
    refine Finset.sum_congr rfl fun b _=>?_ ;simp_rw [shadowed]; exact click _ _ (H _ b) hp hs
def fshade (f : Cover→ℝ)(k:Axis)(v:Cover) := f (v+-step k)-f v
lemma cash_B {Q : Row (TypeFace 2) I}(H: Q.strip σ A)(hs : 0<σ)(hp:Pad f)(i j): scales (composeRows (transRows (cobound 1)) Q i j) f= ∑ b: TypeFace 2,∑ k: Axis,left ℝ 1 k b i* scales (Q b j) (fshade f k):= by
    obtain ⟨E,hE,h⟩:=Next.Free.delta_budget 1 σ
    unfold scales; simp_rw [composeRows,Finset.sum_mul];rw [Summable.tsum_finsetSum]; swap
    · intro t _; exact pay_pivot _ f (width_routed hs.le (fun _=>le_rfl) ((strip_trans h) i t) (fun _=> H _ _)) hp hs
    refine Finset.sum_congr rfl fun b _=> ?_;simp_rw [brought]; simpa only [sub_neg_eq_add, scales, fshade] using click (R:=Q b j) (fun i:Axis=> -step i) _ (H b j) hp hs
lemma Pad.frow (h: Pad f) (k:Axis): Pad (_root_.YM.FormalBulk08.Cork.frow f k) := by
   have he := (h.shift (step k : Cover)).add (h.smul (-1)); simp only [neg_one_smul,←sub_eq_add_neg] at he;exact he
lemma cash_crest {R : Row (TypeFace 2) (TypeFace 2)} (H : R.strip σ A)(hp : Pad f)(hs : 0<σ)(i j): scales (composeRows (composeRows (transRows (cobound 1)) R) (cobound 1) i j) f=
    ∑ b:TypeFace 2, ∑ k: Axis,left ℝ 1 k b j * (∑ u: TypeFace 2,∑ a: Axis,left ℝ 1 a u i * scales (R u b) (fshade (frow f k) a)):= by
   obtain ⟨E,hE,h⟩:= Next.Free.delta_budget 1 σ
   rw [cash_X (strip_compose hs.le (strip_trans h) H) hs hp]; simp_rw [cash_B H hs (hp.frow _)]
end YM.FormalBulk08.Cork
