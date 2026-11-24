import YM.PertExtension.Aspiration
import YM.Comparison.RG02.Order.Pay
/-!
# Finite-regulator *through n* unique jet, one marker frame

 Keep polynomial truncation bills separately at each pin. `Trial`
 extends earlier aspir statements without buying all orders at once. All
 times real positive germ of exact quarter-step square. No control of size.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory RG
open Marker Multi Order PertExtension.Series PertExtension.Series.Tested
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x y f g : ℝ→E} {a b : ℕ→E}

def Trial (a : ℕ→E) (f : ℝ→E) (n : ℕ) := Bill (n+1) (f-peval a n)
abbrev along : Filter ℝ := Tested.germ

omit [NormedSpace ℝ E] in
lemma bill_zero : Bill n (0:ℝ→E) := ⟨0,le_rfl,Eventually.of_forall fun _=>by simp⟩
lemma bill_sum {ι:Type*} (S : Finset ι) (x:ι→ℝ→E) (h : ∀ i∈S, Bill n (x i)) : Bill n (∑ i∈S,x i) := by
   induction S using Finset.induction with
   | empty=> rw [sum_empty]; exact bill_zero
   | insert i s hi ih=> rw [Finset.sum_insert hi]; exact bill_add (h i (mem_insert_self ..)) (ih (fun i hj=> h i (mem_insert_of_mem hj)))
omit [NormedSpace ℝ E] in
lemma bill_congr (he : x=ᶠ[along] y) (h : Bill n x) : Bill n y := by obtain ⟨C,c,h⟩:=h; exact ⟨C,c,h.congr (he.mono fun _ hx=>by rw [hx])⟩
lemma bill_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) {x:ℝ→E} (hb : Bill (R:=E) n x) : Bill n (c • x) := by
   obtain ⟨C,H,h⟩:=hb; refine ⟨‖c‖*C,mul_nonneg (norm_nonneg _) H,h.mono fun i hi=>?_⟩; rw [Pi.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

lemma trial_congr (u : x=ᶠ[along] y) (h : Trial a x n) : Trial a y n := bill_congr (u.sub (EventuallyEq.rfl)) h
lemma trial_flow (h : Trial a f n) (hv : ∀ i≤n,a i=b i) : Trial b f n := by
   have he : peval b n=peval a n:= funext fun r=> Finset.sum_congr rfl fun i hi=> congrArg (r^i • ·) (hv i (mem_range_succ_iff.mp hi)).symm
   unfold Trial; rw [he]; exact h
lemma trial_drop {n : ℕ} (h : Trial a f (n+1)) : Trial a f n := by
   have he : peval a (n+1)=peval a n+(fun t:ℝ=>t^(n+1)•a (n+1)):= funext fun x=> sum_range_succ ..
   have hh:= bill_mon (a (n+1)) (n+1) (le_refl _)
   unfold Trial at *
   have hv: f-peval a n=f-peval a (n+1)+(fun t:ℝ=>t^(n+1)•a (n+1)) := by rw [he]; abel
   rw [hv]; exact bill_add (bill_ge h (by omega)) hh
lemma trial_earlier (hm : m ≤ n) (h : Trial a f n) : Trial a f m := by
   induction hm with
   | refl=> exact h
   | step h ih=> exact ih (trial_drop h)
lemma trial_gap (h : Trial a f n) (he : Trial b f n) : ∀ i≤n,a i=b i:= by
   intro i hi; induction i using Nat.strong_induction_on with | _ i ih
   obtain ⟨A,hA,ha⟩:= trial_earlier hi h
   obtain ⟨B,hB,hb⟩:= trial_earlier hi he
   by_contra hh; let r:=‖a i-b i‖; have hr : 0<r:= norm_pos_iff.mpr (sub_ne_zero.mpr hh)
   obtain ⟨t,h1,h2,hp,heq⟩:= (ha.and (hb.and (eventually_small (show 0 < r/(A+B+1) from div_pos hr (by positivity))))).exists
   have hz:= (lt_div_iff₀ (by positivity)).mp heq
   have hq : ‖peval a i t-peval b i t‖ ≤ (A+B)*t^(i+1) := by
      rw [show peval a i t-peval b i t=(f-peval b i) t-(f-peval a i) t by simp only [Pi.sub_apply]; abel]
      exact (((norm_sub_le ..).trans (add_le_add h2 h1))).trans_eq (by ring)
   have ht : peval a i t-peval b i t=t^i • (a i-b i):= by
      unfold peval Zone.eval; rw [Finset.sum_range_succ,Finset.sum_range_succ,smul_sub,show (∑ j∈ range i,t^j • a j)=(∑ j∈range i,t^j • b j) by
        exact Finset.sum_congr rfl (fun j hj=> congrArg (t^j • ·) (ih j (mem_range.mp hj) (by simp only [mem_range] at hj; omega)))]; abel
   rw [ht,norm_smul,Real.norm_of_nonneg (pow_nonneg hp.le _),pow_succ] at hq
   have ht : r ≤ (A+B)*t := (mul_le_mul_iff_right₀ (pow_pos hp i)).mp (hq.trans_eq (by ring))
   linarith only [hp,ht,hz]
lemma trial_sample (h : Trial a f n) : Tendsto f along (𝓝 (a 0)) := Metric.tendsto_nhds.mpr fun ε he=>by
  obtain ⟨C,hC,h⟩:= trial_earlier (Nat.zero_le _) h
  filter_upwards [h,eventually_small (show 0<ε/(C+1) by positivity)] with t ht hz
  simp [peval,Zone.eval] at ht; rw [dist_eq_norm_sub]; nlinarith [(lt_div_iff₀ (by positivity:0<C+1)).mp hz.2]

lemma eval_constant (a : ℕ→ℂ) (z : ℂ) : peval (z • a) m=z • peval a m := by
   ext1 t; simp_rw [peval,Pi.smul_apply,Zone.eval, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> by simp [Complex.real_smul,mul_left_comm]
lemma eval_add (x y : ℕ→E) : peval (x+y) n=peval x n+peval y n := by funext t; simp_rw [peval,Zone.eval,Pi.add_apply,smul_add,Finset.sum_add_distrib]; rfl
lemma trial_add (h : Trial a f n) (p : Trial b g n) : Trial (a+b) (f+g) n := by
   unfold Trial; rw [eval_add, show f+g-(peval a n+peval b n)=(f-peval a n)+(g-peval b n) by abel]; exact bill_add h p
lemma trial_scale {a : ℕ→ℂ} {f : ℝ→ℂ} (z : ℂ) (h : Trial a f n) : Trial (z • a) (z • f) n:= by unfold Trial; rw [eval_constant, ← smul_sub]; exact bill_smul z h

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
def detail (x : Grade R n) (s : R.Mode) := fun i=> (observe R n x i).part s
lemma tests (x : Grade R n) (s : R.Mode) (t : ℝ) : peval (detail x s) n t = (value (t:ℂ) x).part s := by
   unfold peval Zone.eval detail; rw [vpart]; simp [Complex.real_smul]
lemma tests_origin (x : Grade R n) (h : Order.UnitLeading x) : detail x R.quiet 0=1 := by
   have he:=observed (x:=x) R.quiet (Nat.zero_le n)
   simp only [Nat.factorial_zero,Nat.cast_one,one_mul] at he
   have hh : pick n 0=(indices n).quiet := Subtype.ext (card_eq_zero.mp (picked n (Nat.zero_le _)))
   rw [hh,Join.pair_quiet,h] at he; exact he
end YM.Comparison.RG02.Laplace
