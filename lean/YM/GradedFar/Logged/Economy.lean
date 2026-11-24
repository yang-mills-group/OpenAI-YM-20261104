import YM.GradedFar.Logged.HorizonFork

/-!
# Prices with physical-log exponents

Towards (G.5) by method of OPE/Orbits (Receipts & Fee) with full logs.
This lets period & UV remain taken in actual table, not any future radius
arrangement with test moving through cutoffs. Relative to genuine LogTrace
hypothesis as in BB.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Economy
open Finset Filter Function Set Spec Table Extraction OPE OPE.Log Asymptotics
open scoped Topology Classical BigOperators
variable {I J M E A F:Type} [NormedAddCommGroup E]
structure Small (I:Type) where
    p: Filter I
    r: I→ℝ
    leaps:Tendsto r p (𝓝[>](0:ℝ))
namespace Small
variable (Q:Small I)
lemma positive:∀ᶠ i in Q.p,0<Q.r i:=Q.leaps.eventually self_mem_nhdsWithin
lemma bounded:∀ᶠ i in Q.p,Q.r i≤1:= ((tendsto_nhdsWithin_iff.mp Q.leaps).1.eventually_lt_const zero_lt_one).mono fun i hi=>hi.le
lemma ran:∀ᶠ i in Q.p,1≤badge (Q.r i):=(Q.positive.and Q.bounded).mono (fun i h=> (by
    unfold badge run; linarith [Real.log_nonpos h.1.le h.2]))
end Small
local notation "τ"=>𝓝[>] (0:ℝ)
variable (Q:Small I)
def Paint (Q:Small I) (W:I→ℝ)(f:I→E): Prop := ∃ C:ℝ, 0<C ∧ ∃ k:ℕ, ∀ᶠ i in Q.p,
     ‖f i‖≤C*(badge (Q.r i))^k * |W i|
variable {Q}
namespace Paint
variable {T U:I→ℝ}{P:Small I}{f g h:I→E}
lemma from_cost (C:ℝ)(hC:0<C)(k:ℕ)(h : ∀ᶠ i in Q.p, ‖f i‖≤ C*(badge (Q.r i))^k*T i) : Paint Q T f:= by
    refine ⟨C,hC,k,?_⟩; filter_upwards [h,Q.ran] with i hi hp; apply hi.trans; have h0 : 0 < badge (Q.r i):=zero_lt_one.trans_le hp; gcongr; exact le_abs_self _ /- · have h0:0<badge (Q.r i):=zero_lt_one.trans_le hp; positivity
                                                                                exact le_abs_self _ -/
lemma assists (h : Paint Q T f) (he : ∀ᶠ i in Q.p,f i = g i): Paint Q T g:=by obtain ⟨C,H,k,h⟩:=h; exact ⟨C,H,k,(he.and h).mono fun i h=> h.1 ▸ h.2⟩
lemma of_le [NormedAddCommGroup F]{g:I→ F}(h: Paint Q T f)(he:∀ᶠ i in Q.p,‖g i‖≤‖f i‖): Paint Q T g:= by obtain ⟨C,H,k,h⟩:=h; exact ⟨C,H,k,(he.and h).mono fun i h=>h.1.trans h.2⟩
lemma eases (h: Paint Q T f)(he:∀ᶠ i in Q.p,|T i|≤|U i|): Paint Q U f:= by
   obtain ⟨C,H,k,h⟩:=h; refine ⟨C,H,k,(he.and (h.and Q.ran)).mono fun i ⟨h,h',hh⟩ => ?_⟩; apply h'.trans; exact mul_le_mul_of_nonneg_left h (mul_nonneg H.le (pow_nonneg (zero_lt_one.trans_le hh|>.le) k))
lemma plus (h:Paint Q T f)(hx:Paint Q T g): Paint Q T (fun i=> f i+g i):= by
    obtain ⟨C,hC,k,h⟩:=h; obtain ⟨B,hB,p,hx⟩:= hx
    refine ⟨C+B,add_pos hC hB,k+p,?_⟩; filter_upwards [Q.ran, h,hx] with i hs h hx; apply (norm_add_le ..).trans; apply le_trans (add_le_add h hx); rw [add_mul,add_mul]; gcongr <;> first| exact hs | omega
lemma neg (h:Paint Q T f):Paint Q T (fun i=> - f i):= h.of_le (Eventually.of_forall fun _=> (norm_neg _).le)
lemma minus (h:Paint Q T f)(hx:Paint Q T g):Paint Q T (fun i=> f i-g i):= by simp_rw [sub_eq_add_neg]; exact plus h hx.neg
lemma none {Q:Small I} : Paint Q T (fun _=> (0:E)):= by
    refine ⟨1,zero_lt_one,0,?_⟩; filter_upwards with i; rw [norm_zero,pow_zero,one_mul,one_mul]; positivity
lemma sum {B:J→ I→E}(s:Finset J)(h:∀j∈s,Paint Q T (B j)):Paint Q T (fun i=> ∑j∈s,B j i):=by
    induction s using Finset.induction_on with| empty=> simp_rw [Finset.sum_empty]; exact none | insert j s hj ih=> simp_rw [Finset.sum_insert hj]; exact Paint.plus (h _ (Finset.mem_insert_self ..)) (ih fun _ h'=> h _ (Finset.mem_insert_of_mem h'))
lemma bounded (C:ℝ)(h : ∀ᶠ i in Q.p, ‖f i‖≤C): Paint Q (fun _=>1) f := by refine ⟨max C 1,lt_max_of_lt_right zero_lt_one,0,?_⟩; simp only [pow_zero,mul_one,abs_one]; exact h.mono fun i h=> h.trans (le_max_left ..)
lemma const (x:E) : Paint Q (fun _=>1) (fun _=> x) := Paint.bounded ‖x‖ (by filter_upwards with i; exact le_rfl)
lemma pull (h: Paint Q T f) {P:Small J}{g:J→ I}(hg:Tendsto g P.p Q.p)(hi : ∀ᶠ j in P.p,P.r j≤Q.r (g j)): Paint P (T ∘ g) (f ∘ g):= by
    obtain ⟨C,hC,k,h⟩:=h; refine ⟨C,hC,k,?_⟩; filter_upwards [hg.eventually h,hg.eventually Q.ran,hi,P.positive] with j hj (hp : 1 ≤ badge (Q.r (g j))) hi hs;
    apply hj.trans; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hp]) ?_ _) hC.le) (abs_nonneg _)
    unfold badge run; linarith only [Real.log_le_log hs hi]
lemma times_cost [NormedAddCommGroup F] [NormedAddCommGroup M] {x:I→F}{y:I→M} (h:Paint Q T f)(hp: Paint Q U x)
    (he:∀ᶠ i in Q.p,‖y i‖ ≤ ‖f i‖*‖x i‖): Paint Q (fun i=> T i*U i) y:=by
    obtain ⟨C,hC,k,h⟩:=h; obtain ⟨B,hB,l,hp⟩:=hp
    refine ⟨C*B,mul_pos hC hB,k+l,?_⟩; filter_upwards [h,hp,he] with i h hp he;
    apply (he.trans (mul_le_mul h hp (norm_nonneg _) ((norm_nonneg _).trans h))).trans_eq; rw [abs_mul,pow_add]; ring
lemma scales {g:I→ℂ} [NormedSpace ℂ E] (h:Paint Q T f) (hg:Paint Q U g) : Paint Q (fun i=> U i*T i) (fun i=>g i • f i) := hg.times_cost h (Eventually.of_forall fun _=> (norm_smul ..).le)
lemma scales_r {g:I→ℝ} [NormedSpace ℝ E] (h:Paint Q T f) (hg:Paint Q U g) : Paint Q (fun i=> U i*T i) (fun i=>g i • f i) := hg.times_cost h (Eventually.of_forall fun _=> (norm_smul ..).le)
lemma times {f g:I→ℂ}(h:Paint Q T f)(hg:Paint Q U g): Paint Q (fun i=> T i*U i) (fun i=> f i*g i) := h.times_cost hg (Eventually.of_forall fun _=> (norm_mul ..).le)
lemma by_real {f g:I→ℝ}(h:Paint Q T f)(hg: Paint Q U g): Paint Q (fun i=>T i*U i) (fun i=>f i*g i) := h.times_cost hg (Eventually.of_forall fun _=> (norm_mul ..).le)
lemma norm (h: Paint Q T f): Paint Q T (fun i=> ‖f i‖) := h.of_le (Eventually.of_forall fun _=> (Real.norm_of_nonneg (norm_nonneg _)).le)
end Paint
end YM.OPE.Logged.Economy
