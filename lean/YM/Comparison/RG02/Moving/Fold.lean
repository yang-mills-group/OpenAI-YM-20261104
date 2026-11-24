import YM.Comparison.RG02.Moving.Tissue
/-!
# Diagonal folding

Fuse Taylor lift of a markerized orbit with the original marker board. Maps two *distinguished*
coupling markers (outer for remainder budget of derivative transformations on entrywise
 ideal near-V tensors, inner for the usual vertex arguments) to the same powers. Doesn't mix distinct
 stochastic data; boil_joint used per-Mode at the very end. After this operation
 the formal value multiplication is compatible again, even with moving entries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving.Shift
open Function Filter Finset MeasureTheory YM.Marker YM.Multi Order Assembly Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace Path
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open scoped Topology BigOperators Classical ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V) (r : ℕ)
local notation "δ" => Grade R r
local notation "M" => Board R r
local notation "ψ" => axis R r
lemma nil_tip (k : ℕ) (he : r < k) : (axis R r) ^ k = 0 := by
   apply Join.both_parts; intro s t
   rw [← series_x, ← map_pow, polarization, PowerSeries.coeff_X_pow, if_neg (ne_of_lt ((order_limit r t).trans_lt he)), Poly.part_nil,Poly.part_nil,mul_zero]

def nilRead : Polynomial (Grade R r) →+* Grade R r := Polynomial.eval₂RingHom (RingHom.id _) ψ
lemma nil_sector (z : δ) (k:ℕ) : nilRead R r (Polynomial.monomial k z)= z * ψ ^ k := Polynomial.eval_monomial ..
lemma nil_cost (p:PowerSeries (Grade R r)) : nilRead R r (PowerSeries.trunc (r+1) p)=∑ i∈range (r+1), PowerSeries.coeff i p * ψ ^ i := PowerSeries.eval₂_trunc_eq_sum_range ..
lemma nil_forget (p:Polynomial (Grade R r)) : nilRead R r (PowerSeries.trunc (r+1) p)= nilRead R r p := by
   induction p using Polynomial.induction_on' with
   | add p q hp hq=> rw [Polynomial.coe_add,map_add,map_add,map_add,hp,hq]
   | monomial i a=>
      rw [nil_cost,nil_sector,Polynomial.coe_monomial]; simp_rw [PowerSeries.coeff_monomial,ite_mul,zero_mul]; rw [Finset.sum_ite_eq']; split
      · rfl
      next h=> rw [nil_tip _ _ _ (by simp only [mem_range] at h; omega),mul_zero]

def fuse (H : ℝ→Grade R r) := nilRead R r (PowerSeries.trunc (r+1) (tissue H))
lemma fuse_time (H : ℝ→Grade R r) : fuse R r H=∑ i∈ range (r+1), sight H i* ψ ^i := by
   rw [fuse,nil_cost]; simp_rw [tissue,PowerSeries.coeff_mk]


variable {R r} {P Q : ℝ→Grade R r} (h : Seen P) (p : Seen Q)
lemma fuse_save (x:Grade R r) : fuse R r (fun _=>x)=x := by rw [fuse,constant_series,PowerSeries.trunc_C]; exact Polynomial.eval_C
lemma fuse_congr (hv : P=ᶠ[𝓝 0] Q) : fuse R r P=fuse R r Q := by rw [fuse_time,fuse_time]; simp_rw [sight_congr hv]
include h p
lemma fuse_add : fuse R r (P+Q)= fuse R r P+fuse R r Q := by unfold fuse; rw [h.adds p,map_add,map_add]
lemma fuse_prod : fuse R r (P*Q)=fuse R r P*fuse R r Q := by
   unfold fuse; rw [h.multiplies p, ← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul,nil_forget, map_mul]
omit p
lemma fuse_scale (z:ℂ) : fuse R r (z • P)= z • fuse R r P := by
  rw [fuse_time,fuse_time,Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [Seen.scaled h z,smul_mul_assoc]
lemma fuse_pow (n:ℕ) : Seen (P^n) ∧ fuse R r (P^n)=fuse R r P ^ n := by induction n with
  | zero=> rw [pow_zero,pow_zero]; exact ⟨Seen.even 1,fuse_save _⟩
  | succ n ih=> rw [pow_succ,pow_succ,fuse_prod ih.1 h,ih.2]; exact ⟨ih.1.product h,rfl⟩
omit h in
lemma fuse_sum {I : Type*} (S : Finset I) (F : I→ℝ→Grade R r) (h : ∀ i∈S,Seen (F i)) : fuse R r (∑ i∈S,F i)=∑ i∈S,fuse R r (F i):= by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; exact fuse_save _
  | @insert i S hi ih=>rw [sum_insert hi,sum_insert hi,fuse_add (h i (mem_insert_self ..)) (Seen.sum _ _ (fun j hj=>h j (mem_insert_of_mem hj))), ih (fun j hj=> h j (mem_insert_of_mem hj))]

end YM.Comparison.RG02.Moving.Shift
