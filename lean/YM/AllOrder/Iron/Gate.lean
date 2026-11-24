import YM.AllOrder.Iron.Bounds
import YM.AllOrder.Iron.Rim
import YM.Next.STATIONARY.Films.ThinTrace
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
variable (i: G.ColorIndex)
open Wilson Precision
open Bloch Laurent Audience Push.Uniform
section weights
variable (n:Side){α β γ : Type}[Fintype β]{a:α→Site n}{b:β→Site n}{c0:γ→Site n}{η C₀ D:ℝ} {M:Matrix α β ℝ}{N:Matrix β γ ℝ}
abbrev Capped (n:Side)(a:α→Site n)(b:β→Site n)(η:ℝ)(C:ℝ)(M:Matrix α β ℝ):= ∀ i j,|M i j| ≤ C*Push.Uniform.Decay η (a i) (b j)
variable {n}
omit [Fintype β] in
lemma closing (hp:0≤η)(hx:0≤C₀)(q:ℕ)(he:∀ x y,|M x y| ≤ C₀ ∧ (q<separation (a x) (b y)→ M x y=0)) : Capped n a b η (C₀ *Real.exp (η*q)) M:= by
   intro x y; by_cases h:q<separation (a x) (b y);
   · rw [(he x y).2 h,abs_zero]; exact mul_nonneg (mul_nonneg hx (Real.exp_pos _).le) (decay_pos ..).le
   apply (he x y).1.trans; rw [mul_assoc]; apply le_mul_of_one_le_right hx; rw [Decay,← Real.exp_add]; apply Real.one_le_exp; have hb : (separation (a x) (b y):ℝ)≤q:=by exact_mod_cast le_of_not_gt h
   nlinarith only [mul_le_mul_of_nonneg_left hb hp]
omit [Fintype β] in
lemma Capped.mono (h:Capped n a b η C₀ M) {η':ℝ}(hp:η'≤η) (hc:0≤C₀) : Capped n a b η' C₀ M:= fun i j=> (h i j).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hp) (by positivity))) hc)
omit [Fintype β] in
lemma Capped.flip (h:Capped n a b η C₀ M) : Capped n b a η C₀ Mᵀ:= by intro i j; rw [decay_comm]; exact h j i
abbrev metric (η:ℝ)(k:ℕ):= (k:ℝ)*countCost η
lemma Capped.bond (h:Capped n a b (2*η) C₀ M) (p:Capped n b c0 (2*η) D N)(he:0<η){k:ℕ}(q:Multiplicity b k) (hk:0≤C₀)(hx:0≤D): Capped n a c0 η (C₀*D* metric η k) (M*N) := by
  let T := Decay (n:=n) η; intro i j; let a:= a i; let c':=c0 j; have ht(l:β):= decay_step he.le a (b l) c'; have ha : η≤2*η:=by linarith
  calc _ ≤ ∑ l:β,|M i l*N l j|:= Finset.abs_sum_le_sum_abs ..
       _ ≤ ∑ l:β,C₀ * D * Decay η a c' * T a (b l):= Finset.sum_le_sum fun l _=> by
          rw [abs_mul, show _ * T a (b l)=T a (b l)*(C₀*D*T a c') from mul_comm ..]
          have hv:= mul_le_mul (h i l) ((p.mono ha hx) l j) (abs_nonneg _) ((abs_nonneg _).trans (h i l))
          refine hv.trans ?_; rw [show Decay (2*η) a (b l)=T a (b l)*T a (b l) from (by unfold T Decay; rw [← Real.exp_add]; congr 1; ring)];
          have hf := mul_le_mul_of_nonneg_left (ht l) (show 0 ≤ C₀*D*T a (b l) from mul_nonneg (mul_nonneg hk hx) (decay_pos ..).le); unfold T a c' at *; linarith only [hf]
       _ ≤ _ := by rw [← Finset.mul_sum,mul_right_comm C₀] -- fix
                   have hQ:= mul_le_mul_of_nonneg_left (q.count b he a) (mul_nonneg (mul_nonneg hk hx) (decay_pos η a c'|>.le)); unfold T metric a c' at *; linarith only [hQ]
end weights
variable (S)
def count (L:Side)(G:Gauge):= Fintype.card (ParcelG G L)
lemma crowd : Multiplicity (addressJ S (G:=G)) (count S.patch.L G):= by
    intro x; let T:=ParcelG G S.patch.L; let Q:=clothe G S; let C0:=univ.filter (fun a:Bodies G c f=> addressJ S a=x); change C0.card ≤ count S.patch.L G; suffices Set.InjOn (fun a => (Q a).2) ↑C0 from (card_le_card_of_injOn _ (fun _ _=>mem_univ _) this); exact fun i hi j hj h=> Q.injective (Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) h)
end YM.AllOrder.Iron
