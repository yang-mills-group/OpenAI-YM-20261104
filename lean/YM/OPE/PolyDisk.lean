import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.Lagrange

/-! Finite Banach-valued interpolation estimate for a bounded observable on a
thermal disk (before apply matrix elements or characters). The cost of the
label bound will not be raised by the high order of interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.PolyDisk
open scoped BigOperators Classical Topology
open Function Filter Set Complex Polynomial

section Taylor
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable (f : ℂ → V) (κ B : ℝ)

private def derivCoeff (n:ℕ) := ((Nat.factorial n : ℂ)⁻¹) • (iteratedDeriv n f 0)
private def series (x : ℂ) (n:ℕ) := x^n • derivCoeff f n

/-- Taylor estimate by geometric summation of Cauchy's bound. -/
lemma TaylorCap (hκ : 0<κ) (hf : DiffContOnCl ℂ f (Metric.ball 0 κ)) (hb : ∀ z∈Metric.sphere 0 κ, ‖f z‖ ≤ B) :
    ∃ (c : ℕ→V), ∀ (x:ℂ) (A : ℕ), ‖x‖ ≤ κ/2 → ‖f x - ∑ n∈Finset.range A, x^n • c n‖ ≤ 2*(B*(‖x‖/κ)^A) := by
  refine ⟨derivCoeff f,fun x A hx' => ?_⟩
  have hx : x∈Metric.ball 0 κ:=mem_ball_zero_iff.mpr (hx'.trans_lt (half_lt_self hκ))
  let g:=series f x
  have h(t:ℕ): ((Nat.factorial t : ℂ)⁻¹ • (x-0)^t • iteratedDeriv t f 0 : V) = g t := by
    rw [sub_zero]; unfold g series derivCoeff; rw [smul_smul,smul_smul]; rw [mul_comm]
  have he : HasSum g (f x):=(hasSum_taylorSeries_on_ball (c:=0) (f:=f) hf.differentiableOn hx).congr_fun (fun i=>(h i).symm)
  have hv : HasSum (fun n : ℕ=> g (n+A)) (f x-∑ i ∈ Finset.range A, x^i • derivCoeff f i) := by
    rw [← he.tsum_eq]
    change HasSum _ ((∑' n, g n)-(∑ i ∈ Finset.range A, g i))
    rw [← eq_sub_of_add_eq' (Summable.sum_add_tsum_nat_add A he.summable)]
    exact ((summable_nat_add_iff A).mpr he.summable).hasSum
  let p (n):=B*(‖x‖/κ)^n
  have ht(n): ‖g n‖≤p n:=by
    unfold g series derivCoeff p
    rw [norm_smul, norm_smul, norm_pow, norm_inv, Complex.norm_natCast]; calc
      _ ≤ ‖x‖ ^ n * (((Nat.factorial n:ℝ))⁻¹ * ((Nat.factorial n:ℝ)*B/κ^n)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hκ hf hb) (by positivity)) (by positivity)
      _ = _ := by have hN: ((Nat.factorial n:ℝ))≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _); rw [div_pow]; field_simp
  have hu(n):‖g (n+A)‖ ≤ p A * (2⁻¹)^n:= calc
    _ ≤ p (n+A):=ht _
    _ ≤ _ := by
      rw [show p (n+A)=p A*(‖x‖/κ)^n from (by unfold p; rw [Nat.add_comm, pow_add];ring)]
      have hp := (norm_nonneg _|>.trans (ht A))
      gcongr
      rw [div_le_iff₀ hκ]; linarith only [hx']
  have hs : HasSum (fun n : ℕ=> p A *((2⁻¹)^n)) (p A * (1-2⁻¹)⁻¹):= HasSum.const_smul (p A) (hasSum_geometric_of_norm_lt_one (ξ:=(2⁻¹ : ℝ)) (by norm_num))
  calc
    _ ≤ p A * (1-2⁻¹)⁻¹:=HasSum.norm_le_of_bounded hv hs hu
    _ = _ := by unfold p;ring_nf
end Taylor

end YM.OPE.PolyDisk

namespace YM.OPE.PolyDisk
open scoped BigOperators Classical Topology
open Function Filter Set Complex Polynomial

def lagWeight {A:ℕ} (u:ℝ) (i:Fin A) : ℂ:=Polynomial.eval (u:ℂ) (Lagrange.basis Finset.univ (fun j:Fin A=>(j.val:ℂ)) i)
def displacement {A:ℕ} (a u : ℝ) (i:Fin A) := a*((i.val:ℝ)-u)

lemma power_exact {A:ℕ} (a u:ℝ)(n:ℕ)(hn:n<A): ∑ i:Fin A, lagWeight u i * (displacement a u i:ℂ)^n=(0:ℂ)^n := by
   let v:=fun j:Fin A=>(j.val:ℂ)
   let q:= (X-C (u:ℂ))^n
   have hV : Injective v:=fun i j h=> Fin.ext <| Nat.cast_injective (R:=ℂ) h
   have hq : q.degree < Finset.card (α:=Fin A) Finset.univ:=by unfold q; rw [Polynomial.degree_pow,Polynomial.degree_X_sub_C,Finset.card_univ,Fintype.card_fin]; simp [hn]
   have ht:=Lagrange.eq_interpolate (s:=Finset.univ) (f:=q) hV.injOn hq
   have hp(t:ℂ): q.eval t=(t-u)^n := by unfold q; rw [eval_pow,eval_sub, eval_X,eval_C]
   have hz: (∑ i:Fin A, lagWeight u i * (v i-↑u)^n)=(0:ℂ)^n:=by
      simp_rw [← hp]
      rw [← sub_self (u:ℂ),← hp]; conv_rhs => rw [ht]; rw [Lagrange.interpolate_apply,eval_finsetSum]
      simp only [eval_mul,eval_C]
      apply Finset.sum_congr rfl; intro; exact fun _=> mul_comm _ _ 
   calc
     _ = ∑ i : Fin A, (a:ℂ)^n * (lagWeight u i * (v i-↑u)^n):=Finset.sum_congr rfl fun i _=>by unfold displacement v; push_cast; rw [mul_pow];ring
     _ = (a:ℂ)^n * 0^n:= by rw [← Finset.mul_sum, hz]
     _ = _ :=by rw [← mul_pow, mul_zero]

lemma continuous_lag {A:ℕ} (i:Fin A) : Continuous (fun u=> lagWeight u i) := (Polynomial.continuous _).comp Complex.continuous_ofReal

lemma lag_budget (A:ℕ): ∃ C ≥ (1:ℝ), ∀ u:ℝ, |u| ≤ 3 → ∑ i:Fin A, ‖lagWeight u i‖ ≤ C:=by
   let f(u:ℝ) :=∑ i:Fin A, ‖lagWeight u i‖
   obtain ⟨x,hx,h⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (-3:ℝ)≤3)) (show Continuous f from by unfold f; exact continuous_finsetSum _ fun i _=>(continuous_lag i).norm).continuousOn
   exact ⟨max (f x) 1,le_max_right ..,fun u hu=> (h (abs_le.mp hu)).trans (le_max_left ..)⟩

lemma move_budget {A:ℕ} {a u:ℝ} (ha:0 ≤ a) (hu:|u| ≤ 3) (i:Fin A) : |displacement a u i| ≤ a*(A+3):=by
  rw [displacement, abs_mul,abs_of_nonneg ha]; refine mul_le_mul_of_nonneg_left ?_ ha
  have hi₀ : |(i.val:ℝ)|≤A := by rw [abs_of_nonneg (by positivity)]; exact_mod_cast i.is_lt.le
  exact (abs_sub ..).trans (add_le_add hi₀ hu)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
lemma interpolate_cost (A : ℕ): ∃ C > (0:ℝ),∀ (κ B a u:ℝ)(f:ℂ→V), 0<κ → 0 ≤ a → |u|≤3 → a*(A+3)≤κ/2 → DiffContOnCl ℂ f (Metric.ball 0 κ) → (∀ z∈Metric.sphere 0 κ,‖f z‖≤B)→ ‖f 0 - ∑ i:Fin A, lagWeight u i • f (displacement a u i)‖ ≤ C*B*(a/κ)^A:=by
   obtain ⟨C,hC,h⟩:=lag_budget A
   refine ⟨(C+1)*2*(A+3:ℝ)^A,by positivity,fun κ B a u f hκ ha hu haw hf hb=>?_⟩
   have hB : 0 ≤ B:=(norm_nonneg (f κ)).trans (hb _ (Metric.mem_sphere.mpr (by rw [dist_zero_right, Complex.norm_real,Real.norm_of_nonneg hκ.le])))
   obtain ⟨c,hf'⟩:=TaylorCap f κ B hκ hf hb
   let p (x:ℂ):=∑ i ∈ Finset.range A, x^i • c i
   let g:= fun x=> f x-p x
   let z:=fun i:Fin A=>(displacement a u i:ℂ)
   let v:=∑ i:Fin A, lagWeight u i • g (z i)
   have ht (x:ℂ) (hx : ‖x‖≤ a*(A+3)) : ‖g x‖ ≤ 2*(B*((a*(A+3))/κ)^A) := by
       exact hf' x A (hx.trans haw) |>.trans (by gcongr)
   have hz : ‖v‖ ≤ C*(2*(B*((a*(A+3))/κ)^A)):= (norm_sum_le ..).trans <| calc
       (∑ i:Fin A,‖lagWeight u i • g (z i)‖) ≤ ∑ i:Fin A,‖lagWeight u i‖*(2*(B*((a*(A+3))/κ)^A)):=Finset.sum_le_sum (fun i _=>by
           rw [norm_smul]; gcongr; apply ht; unfold z displacement
           rw [Complex.norm_real,Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]; gcongr
           calc |_| ≤ |(i.val:ℝ)| + |u| := abs_sub ..
                _ ≤ _ := add_le_add (le_of_eq (abs_of_nonneg (show (0:ℝ) ≤ i.val by positivity)) |>.trans (  Nat.cast_le.mpr (Fin.is_lt i).le)) hu)
       _ ≤ _ := by rw [← Finset.sum_mul]; gcongr; exact h u hu
   have hp : (∑ i:Fin A, lagWeight u i • p (z i))=p 0:=by
       unfold p; simp_rw [Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun n hn=>?_;
       rw [← Finset.sum_smul]; exact congr_arg (fun ν : ℂ => ν • c n) (power_exact a u n (Finset.mem_range.mp hn))
   calc
     ‖f 0 - ∑ i:Fin A, lagWeight u i • f (z i)‖ = ‖g 0 - v‖:= by congr 1;unfold v g; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib,hp]; abel
     _ ≤ ‖g 0‖+‖v‖:=norm_sub_le ..
     _ ≤ 2*(B*((a*(A+3))/κ)^A) + C*(2*(B*((a*(A+3))/κ)^A)):= add_le_add (ht 0 (by simp [mul_nonneg ha (show 0≤(A:ℝ)+3 by positivity)])) hz
     _ = _ := by rw [show a*(A+3:ℝ)/κ = a/κ * (A+3:ℝ) by ring,mul_pow]; ring
end YM.OPE.PolyDisk
