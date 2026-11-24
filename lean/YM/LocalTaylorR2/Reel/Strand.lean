import YM.LocalTaylorR2.Reel.Spins
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.Eval.Degree
/-! # Sampling prices for Taylor polynomials
 Explicit Cauchy style difference upper. ℓ dependence all on the display `spelling`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Finset Matrix
open scoped BigOperators Classical
abbrev Strand: Type := Icc (-1:ℝ) 1
namespace Strand
-- collar params
def bud : Strand:= ⟨0,by simp⟩
def endB : Strand:= ⟨-1,by simp⟩
def lip : Strand:= ⟨1,by simp⟩
def dial (x:Strand):ℝ:=x
variable {E:Type*}[AddCommGroup E][Module ℝ E]
variable {P:Submodule ℝ E}{f:Strand→E}{n:ℕ} {ι:Type*}[Fintype ι]
lemma teller (q:Strand) (h: Filled P n dial f)(s:ι→Strand)(f':ι→ℝ)(hm : ∀ k≤n,(q:ℝ)^k-(0:ℝ)^k = ∑ i,f' i*((s i:ℝ)^k)):
   f q-f bud=∑ i, f' i • f (s i):= by
   induction h with
   | shoots k hk x _=> 
     simp_rw [smul_smul]; change (q:ℝ)^k • x- (0:ℝ)^k • x=_; rw [← sub_smul,hm k hk,Finset.sum_smul]; rfl
   | @adds f g h h' ih ih'=> simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib,← ih,← ih']; abel
variable {n:ℕ}
def needle (j:Fin 3): Strand:= ![bud,lip,endB] j
def weft (q:Strand)(i:Fin 3):ℝ:= ![-(q:ℝ)^2,((q:ℝ)^2+q)/2,((q:ℝ)^2-q)/2] i
lemma rookie (q:Strand) (h:Filled P 2 dial f): f q-f bud=∑ i, weft q i • f (needle i):= by
   apply teller q h
   intro k hk; interval_cases k <;> simp [Fin.sum_univ_succ,weft,bud,needle,lip,endB] <;> ring
lemma tinyB (q:Strand) (h:0≤(q:ℝ)): ∑ i, |weft q i| ≤ 3*(q:ℝ):= by
   let t:ℝ:=q; have hp:t≤1:=q.2.2; change 0≤t at h
   have hk :0≤(t^2+t)/2:=by positivity
   have hh:(t^2-t)/2 ≤0:=by nlinarith
   have hv: ∀ (A : Fin 3 → ℝ), (∑ i,A i)= A 0+A 1+A 2:= by intro x; simp [Fin.sum_univ_succ]; ring
   rw [hv]; change |-t^2| + |(t^2+t)/2| + |(t^2-t)/2| ≤ 3*t
   rw [abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hk, abs_of_nonpos hh]; nlinarith
-- C_l explicit. NO polynomial-in-l claim; potentially expensive.
def stems (i:Fin (n+1)):Strand:= ⟨ (i.val:ℝ)/(n+1), ⟨by apply le_trans (b:=0) (by norm_num) (by positivity), (div_le_one (by positivity)).mpr (show (i.val:ℝ) ≤ n+1 by exact_mod_cast i.isLt.le) ⟩⟩
def base (i:Fin (n+1)): Polynomial ℝ:= Lagrange.basis univ (dial ∘ stems (n:=n)) i
def tolling (q:Strand)(i:Fin (n+1)):ℝ:= (base i).eval (q:ℝ)-(base i).eval 0
lemma story (j k:ℕ)(hk:k≤j)(x:ℝ): x^k= ∑ i:Fin (j+1),(base i).eval x*((stems i:ℝ)^k):= by
   let g:=dial ∘ stems (n:=j); have h : Injective g := by
      intro a b he; apply Fin.ext; change (a.val:ℝ)/(j+1) = (b.val:ℝ)/(j+1) at he; field_simp at he; exact_mod_cast he
   let X: Polynomial ℝ:= Polynomial.X^k
   have hc: X.degree < ((Finset.univ:Finset (Fin (j+1))).card:WithBot ℕ):= by unfold X; rw [Polynomial.degree_X_pow,card_univ,Fintype.card_fin]; exact_mod_cast (Nat.lt_succ_of_le hk)
   have hp:= Lagrange.eq_interpolate (f:=X) h.injOn hc
   apply_fun Polynomial.eval x at hp; simp_rw [X,Lagrange.interpolate_apply,Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hp
   exact hp.trans (sum_congr rfl fun i _=> mul_comm ..)
lemma rates (q:Strand)(h:Filled P n dial f): f q-f bud=∑ i:Fin (n+1), tolling q i • f (stems i):= by
   apply teller _ h
   intro k hk; simp_rw [tolling,sub_mul,Finset.sum_sub_distrib, ←story n k hk]
def ink (P:Polynomial ℝ):ℝ:= ∑ i ∈ Finset.range (P.natDegree+1), |P.coeff i|
def spelling (n:ℕ):ℝ:=∑ i:Fin (n+1), ink (base i)
lemma ink_pos (P:Polynomial ℝ):0 ≤ ink P:= Finset.sum_nonneg (fun _ _=> abs_nonneg _)
lemma spelling_pos (n:ℕ):0≤spelling n:=Finset.sum_nonneg fun _ _=>ink_pos _
lemma pricedT {x:ℝ} (hx:0≤x)(hv:x≤1)(P:Polynomial ℝ): |P.eval x-P.eval 0| ≤ ink P*x:= by
   rw [ink,Finset.sum_mul,Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]; apply le_trans (Finset.abs_sum_le_sum_abs ..); apply Finset.sum_le_sum
   intro i _; rw [← mul_sub,abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
   rcases i with _|i
   · simpa
   rw [zero_pow (by omega : i.succ ≠ 0),sub_zero,abs_of_nonneg (pow_nonneg hx _),pow_succ]; exact mul_le_of_le_one_left hx (pow_le_one₀ hx hv)
lemma legacy (q:Strand)(hp:0≤(q:ℝ)) (n:ℕ) : ∑ i:Fin (n+1),|tolling q i| ≤ spelling n * (q:ℝ):= by
   unfold spelling; rw [Finset.sum_mul]; exact sum_le_sum (fun _ _=>pricedT hp q.property.2 _)
end Strand
end YM.LocalTaylorR2.Reel
