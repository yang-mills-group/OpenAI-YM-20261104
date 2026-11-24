import YM.Comparison.RG02.Order.First
import YM.Comparison.RG02.Order.VacLog
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order.Second
open Function Filter Finset MeasureTheory
open YM.Marker Order YM.Extra.Trajectories
open scoped BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
variable {r : ℕ} [Fintype V]
local notation "B"=> Board R r
local notation "Δ"=>Grade R r

def lit (n : ℕ) : Grade R r →ₗ[ℂ] ℂ := (blank R).toLinearMap.comp (observeL n)
lemma grade (x : Grade R r) (n : ℕ) : lit n x= (observe R r x n).part R.quiet:= rfl
lemma leading (x : Grade R r): lit 0 x=x.part (B).quiet:= First.buc_vac x
variable {x y:Grade R r} (hx : Symmetric x) (he:UnitLeading x)
include hx
lemma confluent (n:ℕ) (hn:n≤r) (hy:Symmetric y): lit n (x*y)=∑ i∈ Finset.range (n+1), lit i x * lit (n-i) y := by
   obtain ⟨p,rfl⟩:=hx; obtain ⟨q,rfl⟩:=hy; rw [grade,← map_mul,observation _ _ _ hn,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Poly.part_sum]
   exact Finset.sum_congr rfl fun i hi=> by rw [Poly.quiet_mul, grade, grade, observation _ _ _ (by have := mem_range.mp hi; omega), observation _ _ _ ((Nat.sub_le ..).trans hn)]

lemma mute (ho : lit 0 x=0) (n:ℕ) {k : ℕ}(hk : k≤r) (h:k<n): lit k (x^n)=0 := by
   induction n generalizing k with
   | zero=>omega
   | succ n ih=> rw [pow_succ',confluent hx k hk (hx.pow n),Finset.sum_eq_zero]; intro i hi; by_cases hp:i=0
                 · subst i; rw [ho,zero_mul]
                 have hl:k-i<n:=by have hv:= Finset.mem_range.mp hi; omega
                 rw [ih ((Nat.sub_le k i).trans hk) hl,mul_zero]
omit hx in
lemma inside (n:ℕ) (i:Grade R r): lit n (denominator i)=lit n i:= by rw [grade,denominator,observe_bottom,pure_marks, if_pos rfl]; rfl
omit hx in
lemma uncolored (n:ℕ) (h:n≠0) (he:n≤r): lit (r:=r) (R:=R) n 1=0 := by rw [grade, ← map_one (series R r), observation _ _ _ he,PowerSeries.coeff_one, if_neg h, Poly.part_nil]
include he
private def P (x : Δ):= 1-denominator x
omit hx in
private lemma meets : lit 0 (P x)=0 := by unfold P; rw [map_sub, inside,leading, Poly.one_part, if_pos rfl, leading,he,sub_self]
omit he in
private lemma symmetric : Symmetric (P x):= Symmetric.one.sub hx.vacant
private lemma funded (n : ℕ) (hn:n≤r) : lit n (logVac x)=∑ i∈range n, (-((i+1:ℕ):ℂ)⁻¹) • lit n ((1-denominator x)^(i+1)) := by
   rw [vacuum_prefix he,logTo,map_sum]; simp_rw [map_smul]; symm; exact Finset.sum_subset (range_mono hn) fun i _ hi => by
     rw [show 1-denominator x=P x from rfl, mute (x:=P x) (symmetric hx) (meets he) (i+1) hn (by have hv:= mt mem_range.mpr hi; omega),smul_zero]
lemma offset_one (hn:1≤r): lit 1 (logVac x)=lit 1 x := by rw [funded hx he 1 hn,Finset.sum_range_succ]; simp [inside,uncolored 1 one_ne_zero hn]
lemma offset_two (hn:2≤r): lit 2 (logVac x)= lit 2 x-((lit 1 x)^2/2:ℂ) := by
   have hb (n) (h : n≤r) (hp:n≠0) : lit n (1-denominator x)= -lit n x := by rw [map_sub,inside, uncolored n hp h,zero_sub]
   have hh: lit 2 (P x^2)= lit 1 x^2 := by
      rw [sq (P x),confluent (symmetric hx) 2 hn (symmetric hx), Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]; simp only [Finset.sum_range_zero, Nat.reduceSub, zero_add,meets he,mul_zero,zero_mul,add_zero]; rw [show P x=1-denominator x from rfl,hb 1 (by omega) one_ne_zero]; ring
   rw [funded hx he 2 hn, Finset.sum_range_succ,Finset.sum_range_succ]; simp only [Finset.sum_range_zero,zero_add,pow_one];
   rw [show 1-denominator x=P x from rfl, show 1+1=(2:ℕ) by norm_num,hh,show P x=1-denominator x from rfl,hb 2 hn (by decide)]
   push_cast; simp only [smul_eq_mul]; ring
end YM.Comparison.RG02.Order.Second
