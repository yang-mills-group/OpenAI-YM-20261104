import YM.RG02.Wick.Program
import YM.Extra.MULTISOURCE_BOUNDS.Root

/-!
# Summable in placement IN A CONNECTED CUMULANT

Telescope tag effects of uncut or cut WINDOW comparison. Inputs are
ordinary coefficient and change-one physical tag norms. Show implication
in connected tensor comparisons *before* paying exponential support and
interpreting histories, i.e. at level of fully aggregated indices. Use also
on small differences. No rate on obtaining those primitive norms claimed.
The radius expansions themselves shouldn't be used as real gas supports.
Dots live at native/coarse sites; projection already needed. Includes
physical tag law occupancy costs per site; may use extra tree tags with
THEIR complete occupancy, or no tree variation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Roots
open Function Finset MeasureTheory Lattice Wilson Marker Extra.Trajectories Marks Wick Wick.Actor
open scoped BigOperators Classical
variable {V X : Type}{I : Type}[DecidableEq I][Fintype I]{D : I → Type}
variable {n : Side}

def dots (o : I → Site n)(x : Site n)(m : ℕ):= univ.filter fun i => separation x (o i)≤m

def within (o : I → Site n)(x : Site n)(m : ℕ)(s t: Wick.Actor.Draw D): Wick.Actor.Draw D:= fun i => if i∈dots o x m then s i else t i

def span (p : ℝ)(k : ℕ) := Real.exp (-p*k)
lemma span_pos (p : ℝ)(k : ℕ) : 0<span p k:=Real.exp_pos _
@[simp] lemma span_zero (p : ℝ): span p 0=1 := by simp [span]
lemma span_order {p q : ℝ}(hp:p≤q)(k : ℕ) : span q k ≤ span p k:= by apply Real.exp_le_exp.mpr; gcongr

def coat (p : ℝ)(k : ℕ):= Real.exp (p*k)
lemma coated (p : ℝ)(k : ℕ) : coat p k * span p k =1:= by unfold coat span; rw [← Real.exp_add]; ring_nf; exact Real.exp_zero

-- Native-volume count; no output size. choose M from 1/radius.
def Pulse (n : Side)(p L : ℝ): Prop := ∀ x:Site n,∑ y:Site n,span p (separation x y)≤ L
lemma paced {p : ℝ}(M : ℕ)(hp : 1/(4*(M:ℝ)+2) ≤ p) : Pulse n p ((2*(16*(M:ℝ)+9))^4):=fun x=>by
   apply le_trans _ (Extra.Multi.torus_kernel x)
   apply sum_le_sum; intro i _; rw [separation_comm i]; refine (span_order hp _).trans_eq ?_; unfold span; congr 1; ring

structure Covers (o : I→Site n)(p L : ℝ) : Prop where
  starts : 1≤L
  reaches (x : Site n): ∑ i:I,span p (separation x (o i))≤L

omit [DecidableEq I] in
lemma Covers.of_occ {o : I→Site n}{p L : ℝ}{κ : ℕ}(hN : Extra.Multi.Occupancy o κ)(H : Pulse n p L) :
    Covers o p (max 1 (κ*L)):=by
   refine ⟨le_max_left ..,fun x=>?_⟩
   apply (hN.weighted (fun y=>span p (separation x y)) (fun _=> (span_pos ..).le)).trans
   exact (mul_le_mul_of_nonneg_left (H x) (Nat.cast_nonneg _)).trans (le_max_right ..)

def costI (p : ℝ) := (1-Real.exp (-p))⁻¹
lemma costI_nonneg {p : ℝ}(h : 0<p): 0<costI p:= by
   unfold costI; rw [inv_pos,sub_pos]; exact (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr h))
lemma span_rate (t : ℕ){p : ℝ}(hp : 0<p) : (∑ i:Fin t,span p i) ≤ costI p:= by
   have hx:= hasSum_geometric_of_lt_one (Real.exp_pos (-p)).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hp))
   rw [Fin.sum_univ_eq_sum_range (fun i=> span p i)]
   have he i : span p i=Real.exp (-p)^i:=by rw [← Real.exp_nat_mul]; unfold span; rw [mul_comm]
   simp_rw [he]; exact (hx.summable.sum_le_tsum _ (fun i _=> pow_nonneg (Real.exp_pos _).le i)).trans_eq hx.tsum_eq

-- tree tag height expansion. finite `z` uniform stand-in.
def layer (o : I→ Site n)(x : Site n)(t : Draw D)(f : Draw D → ℂ) (m : ℕ)(s : Draw D) :=
    if m=0 then f (within o x 0 s t) else f (within o x m s t)-f (within o x (m-1) s t)

lemma available (o : I→ Site n)(x : Site n)(m : ℕ){s u t: Draw D} (h : ∀ i∈dots o x m,s i=u i) :
    within o x m s t=within o x m u t:= by funext i; unfold within; split_ifs with H; rw [h i H]; rfl
lemma touches (o : I→Site n)(x : Site n)(t : Draw D)(f : Draw D→ℂ)(m : ℕ): Needs (layer o x t f m) (dots o x m):= by
   intro s u h
   unfold layer
   split
   next H => subst m; rw [available o x 0 h]
   next H => rw [available o x _ h,available o x (m-1) (s:=s) (u:=u) (fun i hi=> h i (mem_filter.mpr ⟨mem_univ _, le_trans (mem_filter.mp hi).2 (Nat.sub_le m 1)⟩))]

-- Sum of all layers. use after Supports extend Ω.
lemma combined (o : I→Site n)(x : Site n)(m:ℕ)(hx:∀ i,separation x (o i)≤m)(y : Draw D)(v : Draw D→ℂ) :
    (∑ i: Fin (m+1), layer o x y v i)=v:=by
   funext i
   have he(t : ℕ) : ∑ a ∈ range (t+1), layer o x y v a i=v (within o x t i y):= by
      induction t with
      | zero => simp [layer]
      | succ t h => rw [Finset.sum_range_succ,h,layer, if_neg (by omega),Nat.add_sub_cancel]; abel
   rw [Finset.sum_apply,Fin.sum_univ_eq_sum_range (fun j=>layer o x y v j i), he]; congr 1
   funext j; unfold within dots; simp [hx]

-- Require change at one tagged dependency, and with its FULL external
-- position list already held. Different weights on absolute and compare
-- may decrease root→tag fraction first.
structure Tolls (o : I→Site n)(x : Site n)(f : Draw D→ℂ)(p T : ℝ): Prop where
   paid : 0≤T
   base (s : Draw D) : ‖f s‖ ≤ T
   turns (s t : Draw D) (i : I) : (∀ j, j ≠ i → s j=t j) → ‖f s-f t‖ ≤ T*span p (separation x (o i))

namespace Tolls
variable {o : I→Site n}{x : Site n}{f : Draw D→ℂ}{p T : ℝ}

omit [Fintype I] in
lemma many (h : Tolls o x f p T)(F : Finset I)(s t : Draw D)(H : ∀ i,i∉ F→s i=t i):
    ‖f s-f t‖ ≤ T* ∑ i∈F, span p (separation x (o i)):=by
   induction F using Finset.induction_on generalizing s with
   | empty => rw [show s=t from funext fun _=> H _ (notMem_empty _),sub_self,norm_zero,sum_empty,mul_zero]
   | insert i F hi ih =>
     let a := Function.update s i (t i)
     have hp : ‖f a - f t‖ ≤ T*∑ i∈F,span p (separation x (o i)):= ih a (fun j hj=>by
        by_cases he:j=i
        · subst j; simp [a]
        exact (Function.update_of_ne he ..).trans (H j (by simp [he,hj])))
     have hx := h.turns s a i (fun j hj=> by simp [a,hj])
     rw [show f s-f t=f s-f a+(f a-f t) by abel,sum_insert hi,mul_add]
     exact (norm_add_le ..).trans (add_le_add hx hp)

lemma layer_bound {s : ℝ}{L : ℝ}(_hs : 0<s)(h : Tolls o x f (s+p) T)(hv : Covers o s L) (m : ℕ)(u v : Draw D):
    ‖layer o x v f m u‖≤ L*T*span p m := by
    unfold layer; split
    next H => subst m; rw [span_zero,mul_one]; exact (h.base _).trans (le_mul_of_one_le_left h.paid hv.starts)
    next H =>
      let S:= (dots o x m) \ dots o x (m-1)
      have hp := h.many S (within o x m u v) (within o x (m-1) u v) (fun j hj=> by
         unfold within; split_ifs with H1 H2 H3
         · rfl
         · exact False.elim (hj (mem_sdiff.mpr ⟨H1,H2⟩))
         · exact False.elim (H1 (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp H3).2.trans (by omega)⟩))
         rfl)
      have he : (∑ i∈S,span (s+p) (separation x (o i)))≤ L*span p m := by
         calc
          _ = (∑ i∈S,span s (separation x (o i))) * span p m := by
             rw [sum_mul]; refine sum_congr rfl fun i hi=> ?_
             obtain ⟨h₁,h₂⟩:= mem_sdiff.mp hi
             rw [show m=separation x (o i) by simp only [dots,mem_filter,mem_univ,true_and] at h₁ h₂; omega]; unfold span; rw [← Real.exp_add]; congr 1; ring
          _ ≤ _ := by
             refine mul_le_mul_of_nonneg_right (le_trans ?_ (hv.reaches x)) (span_pos p m).le
             exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> (span_pos ..).le)
      refine hp.trans ((mul_le_mul_of_nonneg_left he h.paid).trans_eq ?_); ring
end Tolls
end YM.RG02.Roots
