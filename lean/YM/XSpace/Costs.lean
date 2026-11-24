import YM.XSpace.Sequence
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Filter package for estimates (mostly at finite cutoff)

Useful for assembling many simultaneous limits (e.g. points and probe evaluations
along with UV spacing and varying center shifts) retaining power accuracy. All later
comparisons have to instantiate `Expense.Stretched`. Compact shape filters may be
trivial, no need asserting every compact populated by every mesh. `Rate` on functions
of not necessarily fixed position, first order power-of-spacing approximation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Expense
open Filter Function Set Lattice Asymptotics
open scoped Topology ContDiff BigOperators
variable {ι X J : Type*} (L : Filter ι) (g : ι→ Mesh)

def a (i : ι) := (g i).spacing
def nodes (p : Mesh) := p.p.side.val
def sides (i:ι): ℝ := (nodes (g i):ℝ)
lemma actual (i : ι): 0<a g i := (g i).positive
lemma counted (i : ι): 0<sides g i:=by unfold sides; exact_mod_cast (show 0<nodes (g i) from (g i).p.side.pos)
lemma length (i : ι): (g i).size=a g i*sides g i:=rfl

structure Stretched : Prop where
  endpt : Tendsto (a g) L (𝓝 0)
  pay (k : ℕ): Tendsto (fun i=> (a g i)^k * sides g i) L atTop
namespace Stretched
variable {L g}
lemma horizon (C : Stretched L g): Tendsto (sides g) L atTop:=by simpa using C.pay 0
lemma width (C : Stretched L g): Tendsto (Mesh.size ∘ g) L atTop:= by have ht:= C.pay 1; simpa only [pow_one,← length,Function.comp_def] using ht
lemma smaller (C : Stretched L g) : ∀ᶠ i in L,a g i≤1:= C.endpt.eventually (ge_mem_nhds zero_lt_one)
lemma invertible (C : Stretched L g) : ∀ k : ℕ, (fun i=> (sides g i)⁻¹)=O[L] (fun i=>a g i^k):=by
  intro k; refine IsBigO.of_bound' ?_
  filter_upwards [(C.pay k).eventually_ge_atTop 1] with i hi
  rw [Real.norm_of_nonneg (inv_pos.mpr (counted _ i)).le,Real.norm_of_nonneg (pow_pos (actual g i) k).le]; exact (inv_le_iff_one_le_mul₀ (counted _ i)).2 hi
lemma wider (C : Stretched L g) {f : J → ι} {K : Filter J} (h : Tendsto f K L): Stretched K (g ∘ f):= ⟨C.endpt.comp h,fun k=> (C.pay k).comp h⟩
private lemma run_growth (V : Run) (k : ℕ): ∀ᶠ i:ℕ in atTop,k*i+i ≤ i+V.reserve*i*i := by
  filter_upwards [eventually_ge_atTop k] with i hi
  apply Nat.le_of_sub_eq_zero ?_; have hp: k ≤ V.reserve*i:= hi.trans (Nat.le_mul_of_pos_left _ V.spare); have hh : k*i ≤ V.reserve*i*i := Nat.mul_le_mul_right i hp; omega
lemma runs (V : Run): Stretched atTop V.step:=by
  have h:(1:ℝ)<V.ratio:=by have p:=V.large;exact_mod_cast (show 1<V.ratio by omega)
  refine ⟨V.spacing_end, fun k=> ?_⟩
  have ht (i : ℕ) : 0 < (V.ratio:ℝ)^i:= pow_pos (zero_lt_one.trans h) i
  have he:= Tendsto.const_mul_atTop (show 0<(V.finalSide.side.val:ℝ) by exact_mod_cast V.finalSide.side.pos) (tendsto_pow_atTop_atTop_of_one_lt h)
  refine tendsto_atTop_mono' atTop ?_ he
  filter_upwards [run_growth V k] with i hi
  change ((V.finalSide.side.val:ℝ)*(V.ratio:ℝ)^i)≤ ((↑(V.ratio^i):ℝ)⁻¹)^k * (↑(V.finalSide.side.val*V.ratio^(i+V.reserve*i*i)):ℝ)
  push_cast; rw [← inv_pow,← pow_mul]
  rw [inv_pow,le_inv_mul_iff₀ (ht _),mul_left_comm,← pow_add,Nat.mul_comm i]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.le hi) (by positivity)
end Stretched
variable [NormedAddCommGroup X]

def Rate (f p : ι → X):= (fun i => f i-p i)=O[L] a g
-- Uniformly bounded. Don't assign name T (implicit-exp pressure).
def Cap (f : ι → X):= f=O[L](fun _=>(1:ℝ))
lemma cost_g (C : Stretched L g) : Cap L (a g):= IsBigO.of_bound' (C.smaller.mono (fun i hi => by rw [Real.norm_of_nonneg (actual g i).le,norm_one];exact hi))

variable {L g} {p q r v : ι→ X}
namespace Cap
lemma bounds (h : Cap L v) : ∃ c:ℝ,0<c∧∀ᶠ i in L, ‖v i‖≤c:=by
  obtain ⟨c,hc,H⟩:=(show _=O[L] _ from h).exists_pos; exact ⟨c,hc,by simpa using H.bound⟩
lemma of_bounds (c : ℝ) (h : ∀ᶠ i in L, ‖v i‖ ≤ c): Cap L v:= IsBigO.of_bound c (by simpa using h)
lemma includes (K : Set X) (h : IsCompact K) (hp : ∀ᶠ i in L,v i ∈ K):Cap L v:= by obtain ⟨c,hc⟩:=(h.image continuous_norm).bddAbove; exact of_bounds c (hp.mono (fun i hi=> hc (Set.mem_image_of_mem _ hi)))
lemma const (L : Filter ι) (c : X): Cap L (fun _=>c):= of_bounds ‖c‖ (Eventually.of_forall fun _=> le_rfl)
lemma higher (p : Stretched L g) (h : Cap L v) (H : Rate L g q v): Cap L q:= by
  exact (IsBigO.add (IsBigO.trans H (cost_g L g p)) h).congr_left (by simp)
lemma add (h : Cap L p) (H : Cap L q): Cap L (p+q):= IsBigO.add h H
lemma sub (h : Cap L p) (H : Cap L q): Cap L (p-q):= IsBigO.sub h H
lemma mul {X : Type*} [NormedRing X] {p q : ι → X} (h : Cap L p) (H : Cap L q): Cap L (p*q):= (IsBigO.mul h H).congr_right (by intro i; simp)
end Cap

namespace Rate
lemma bounds (h : Rate L g p q) : ∃ c:ℝ,0<c ∧ ∀ᶠ i in L, ‖p i-q i‖ ≤ c*a g i:= by
  obtain ⟨c,hc,H⟩:=(show _=O[L] _ from h).exists_pos; exact ⟨c,hc,by simpa only [Real.norm_of_nonneg (actual g _).le] using H.bound⟩
lemma introduce (c : ℝ) (h : ∀ᶠ i in L, ‖p i-q i‖ ≤ c*a g i): Rate L g p q:= IsBigO.of_bound c (h.mono fun i hi=> by rw [Real.norm_of_nonneg (actual g i).le]; exact hi)
lemma refl (L : Filter ι) (g : ι → Mesh) (v : ι → X): Rate L g v v:= introduce 0 (Eventually.of_forall (by simp))
lemma trans (h : Rate L g p r) (H : Rate L g r q): Rate L g p q:= IsBigO.triangle h H
lemma congr (h : Rate L g p q) (H : p=ᶠ[L]r) (k : q=ᶠ[L]v): Rate L g r v:= IsBigO.congr' h (H.sub k) (EventuallyEq.refl ..)
lemma add {y : ι → X} (h : Rate L g p r) (H : Rate L g q y): Rate L g (p+q) (r+y):= (IsBigO.add h H).congr_left (fun i=> by simp; abel)
lemma neg (h : Rate L g p r): Rate L g (-p) (-r):= (IsBigO.symm h).congr_left (by intro i; simp; abel)
lemma sum (F H : J → ι → X) (s : Finset J) (h : ∀ i∈ s, Rate L g (F i) (H i)): Rate L g (fun i=> ∑ j∈s,F j i) (fun i => ∑ j∈s,H j i) := by
  unfold Rate; simp_rw [← Finset.sum_sub_distrib]; exact IsBigO.sum h
lemma const_mul {X : Type*} [NormedRing X] {p q : ι → X} (h : Rate L g p q) (z : X): Rate L g (fun i=> z*p i) (fun i=> z*q i):= by unfold Rate; simp_rw [← mul_sub]; exact IsBigO.const_mul_left h z
lemma mul {X : Type*} [NormedRing X] {p r q v : ι → X} (h : Rate L g p q) (H : Rate L g r v) (C : Stretched L g)
    (hb : Cap L q) (hd : Cap L v): Rate L g (p*r) (q*v):=by
  have hu : (fun i=> p i*r i-q i*v i)=fun i=>p i*(r i-v i) +(p i-q i)*v i:=funext fun i=> by rw [mul_sub,sub_mul]; abel
  change (fun i=>p i*r i-q i*v i)=O[L] _; rw [hu]; exact IsBigO.add ((IsBigO.mul (Cap.higher C hb h) H).congr_right (fun i=> one_mul _)) ((IsBigO.mul h hd).congr_right (fun i=> mul_one _))
lemma real {p q : ι → ℝ} (h : Rate L g p q): Rate L g (fun i=>(p i:ℂ)) (fun i=> (q i:ℂ)):= by
  obtain ⟨c,hc,H⟩:=h.bounds; exact introduce c (H.mono fun i hi=> by rw [← Complex.ofReal_sub,Complex.norm_real]; exact hi)
end Rate
end YM.XSpace.Expense
