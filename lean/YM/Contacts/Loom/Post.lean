import YM.Contacts.Loom.Peak
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
variable {x: Frame α E} {n i l:ℕ} {b d σ:ℝ}
abbrev Mint (E α:ℕ→Type):= Shelf E α (fun _=>ℝ)
-- purely finite number of powers. powers already evaluated at running coupling; size clocks.L
variable {P T: ℕ → Mint E α}
def green {X:Type}[AddCommMonoid X] (P:ℕ→X)(n:ℕ):= ∑ i∈Finset.range (n+1), P i
lemma Arms.cheaper {a b:Shelf E α F}(he: a=b)(h:Budget N x k p a): Budget N x k p b:= he ▸ h
lemma Budget.rush {u : Type} (s:Finset u) (a:u→Shelf E α F) (h:∀ u∈s,Budget N x k p (a u)) : Budget N x k p (∑ i∈s,a i):= by
   refine Arms.spoke s a ?_ h; exact Eventually.of_forall fun _=> zero_le_one -- type
namespace Capture
variable {a t:Mint E α}
structure Word (N:Meter)(x:Frame α E) (k n:ℕ)(z:ℝ)(a:Mint E α)(P:ℕ→Mint E α):Prop where
    quiet : z<0 -- Berry lease
    entries (l:ℕ) : l≤n→ Budget N x k (z*l) (P l)
    grade : Budget N x k (z*(n+1)) (a-green P n)
lemma Word.rising (w:Word N x k n p a P): Budget N x k 0 a:= by
   rw [show a= _ from (sub_add_cancel a (green P n)).symm]; exact Arms.sum (Arms.lo w.grade (mul_nonpos_of_nonpos_of_nonneg w.quiet.le (by positivity)) le_rfl) (Budget.rush (range (n+1)) _ (fun i hi=>(w.entries _ (Nat.le_of_lt_succ (mem_range.mp hi))).lo (mul_nonpos_of_nonpos_of_nonneg w.quiet.le (Nat.cast_nonneg i)) le_rfl))
lemma Word.resumes (w:Word N x k n p a P) (h:i≤n): Word N x k i p a P:= by
   induction h using Nat.decreasingInduction with
   | self=> exact w
   | of_succ i h ih=>
      have hx := Arms.lo ih.grade (show p*(((i+1:ℕ):ℝ)+1) ≤ p*(i+1:ℝ) from mul_le_mul_of_nonpos_left (by push_cast; linarith) w.quiet.le) le_rfl; have hr:= ih.entries _ le_rfl; refine ⟨w.quiet,fun n hn=>ih.entries _ (by omega),?_⟩; rw [Nat.cast_add,Nat.cast_one] at hr; refine (show a-green P i=a-green P (i+1)+P (i+1) from ?_) ▸ (hx.sum hr); unfold green; rw [sum_range_succ P (i+1)]; abel
lemma Word.plush (w:Word N x k n p a P) (hi:P 0=0): Budget N x k p a:= by have hh:= ((w.resumes (Nat.zero_le n)).grade); simpa only [Nat.cast_zero,green, sum_range_succ, sum_range_zero,zero_add,hi,sub_zero,mul_one] using hh
lemma Word.sum (w:Word N x k n p a P) (h:Word N x k n p t T): Word N x k n p (a+t) (P+T) := by
   refine ⟨w.quiet,fun i hi=> (w.entries i hi).sum (h.entries i hi), ?_⟩; refine Arms.cheaper ?_ (w.grade.sum h.grade); unfold green; simp_rw [Pi.add_apply,sum_add_distrib]; abel
lemma Word.opp (w:Word N x k n p a P) : Word N x k n p (-a) (-P):= by apply Word.mk w.quiet (fun i hi=> (w.entries i hi).opp); refine Arms.cheaper ?_ w.grade.opp; unfold green; simp only [sum_neg_distrib]; abel
lemma Word.scale (w:Word N x k n p a P)(s:ℝ) : Word N x k n p (s • a) (s • P):= by
   refine ⟨w.quiet,fun i hi=> (w.entries i hi).scale s,?_⟩; refine Arms.cheaper ?_ (w.grade.scale s); unfold green; simp only [smul_sub,Finset.smul_sum, Pi.smul_apply]
lemma Word.zero (hp:p<0): Word N x k n p 0 0:= ⟨hp,fun _ _=> Budget.zero, by unfold green; simp; exact Budget.zero⟩
lemma Word.join {β:Type}(I: Finset β) (a:β→Mint E α)(P:β→ℕ→Mint E α) (h:p<0)(hw:∀ i∈ I,Word N x k n p (a i) (P i)): Word N x k n p (∑ i∈I,a i) (∑ i∈I,P i):= by induction I using Finset.induction with| empty => simp; apply Word.zero h| insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact Word.sum (hw i (mem_insert_self _ _)) (ih (fun _ h=> hw _ (mem_insert_of_mem h)))
-- exact reconstruction using telescoping layer truncation per left slot.
def branch {X:Type}[Semiring X] (U V : ℕ→X)(n:ℕ): X:= ∑ x∈ HasAntidiagonal.antidiagonal n,U x.1* V x.2
def stair {X:Type}[Semiring X] (P:ℕ→ X) : ℕ→ℕ → X
  | 0 =>fun k=> if k=0 then 1 else 0
  | n+1=> branch (stair P n) P
lemma reenact {V:Type}[Semiring V](P T:ℕ→V) : ∑ i∈Finset.range (j+1), P i*(green T (j-i))=green (branch P T) j:= by
   induction j with
   | zero=> simp [green,branch]
   | succ j ih=>
     rw [show green (branch P T) (j+1)=_ from (show green _ (j+1)=green (branch P T) j+ branch P T (j+1) from sum_range_succ ..),← ih,sum_range_succ _ (j+1)];
     have ht i (hi:i≤ j): P i*green T (j+1-i)=P i*green T (j-i)+ P i*T (j+1-i):= by rw [show j+1-i=j-i+1 from by omega,green,sum_range_succ,mul_add]; rfl
     rw [sum_congr rfl (fun i hi=> ht i (Nat.le_of_lt_succ (mem_range.mp hi))),Finset.sum_add_distrib,add_assoc]; apply congr_arg; simp only [Nat.sub_self, show green T 0=T 0 from Finset.sum_range_one T];
     unfold branch; symm; calc
       _ = ∑ i∈Finset.range (j+1+1),P i* T (j+1-i):= (sum_bij (fun a _=> a.1) (fun a ha=> Finset.mem_range.mpr (by have hj:=HasAntidiagonal.mem_antidiagonal.mp ha; omega)) (fun a ha b hb he=> by have hk:= HasAntidiagonal.mem_antidiagonal.mp ha; have h':=HasAntidiagonal.mem_antidiagonal.mp hb; apply Prod.ext he; omega) (fun x hx=>⟨(x,j+1-x), HasAntidiagonal.mem_antidiagonal.mpr (by have he:=mem_range.mp hx; dsimp only; omega),rfl⟩) (fun a ha=> by rw [show j+1-a.1=a.2 from by have H:=HasAntidiagonal.mem_antidiagonal.mp ha; omega]))
       _ = _:= by rw [sum_range_succ _ (j+1),Nat.sub_self]
lemma Word.mul (w:Word N x k n p a P)(h:Word N x k n p t T): Word N x k n p (a*t) (branch P T):= by
    refine ⟨w.quiet, fun i hi=>Budget.rush (antidiagonal i) _ (fun x hx=> (Budget.mul (P x.1) (T x.2) (w.entries _ ?_) (h.entries _ ?_) ?_)), ?_⟩
    · have hf := HasAntidiagonal.mem_antidiagonal.mp hx; omega
    · have hf := HasAntidiagonal.mem_antidiagonal.mp hx; omega
    · have hx : i=x.1+x.2:=(HasAntidiagonal.mem_antidiagonal.mp hx).symm; rw [hx,Nat.cast_add,mul_add]
    refine Arms.cheaper ?_ (Arms.sum (Budget.mul _ _ w.grade h.rising (add_zero _)) (Budget.rush (range (n+1)) (fun i=>P i * (t-green T (n-i))) (fun i hi=>Budget.mul _ _ (w.entries i (Nat.le_of_lt_succ (mem_range.mp hi))) (h.resumes (Nat.sub_le _ _) |>.grade) ?_)))
    · rw [← reenact]; simp_rw [mul_sub, sum_sub_distrib, sub_mul,green, Finset.sum_mul]; abel
    have he:= mem_range.mp hi; rw [Nat.cast_sub (by omega)]; ring
lemma Word.powers (w:Word N x k n p a P)(j:ℕ): Word N x k n p (a^j) (stair P j):= by
   induction j with
   | zero=>
    simp only [pow_zero]; refine ⟨w.quiet,fun i hi=>?_ ,?_⟩
    · by_cases h:i=0; · subst i; simp only [Nat.cast_zero,mul_zero,stair]; exact Budget.tally (fun _=>1) (Rush.settle 1)
      simp [stair,h]; exact Budget.zero
    unfold green; simp [stair]; exact Budget.zero
   | succ j ih=> rw [pow_succ]; exact ih.mul w
end Capture
end
end YM.Contacts.Loom
