import YM.GradedFar.Interpose
/-!
# Cost across short clocks for a fixed polynomial: can control by size of first coefficients,
via neighborhood shrinking (radius eventually asked, so may depend on order).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Cart
open Function Filter Set PowerSeries
open MS.Book.Program MS.Book.Convolve
open scoped Topology BigOperators Classical
variable {I : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f:I→ℕ→E}

lemma power_cost (z y:ℂ){δ:ℝ}(hz:‖z‖≤δ)(hy:‖y‖≤δ)(n:ℕ) : ‖z^(n+1)-y^(n+1)‖ ≤ (n+1:ℕ)*δ^n*‖z-y‖:=by
 have ht:0≤δ:= (norm_nonneg _).trans hz
 induction n with
 | zero=>simp
 | succ n ih=>
   have h : ‖z‖^(n+1) ≤ δ^(n+1):= pow_le_pow_left₀ (norm_nonneg _) hz _
   calc
     _ = ‖z^(n+1)*(z-y)+y*(z^(n+1)-y^(n+1))‖:= by ring_nf
     _ ≤ ‖z^(n+1)*(z-y)‖+‖y*(z^(n+1)-y^(n+1))‖:= norm_add_le ..
     _ ≤ δ^(n+1)*‖z-y‖+δ*((n+1:ℕ)*δ^n*‖z-y‖):= by simp only [norm_mul,norm_pow];
                                                        gcongr
     _ = _:= by push_cast; ring
lemma worldwide {B:ℕ→ℝ}(hB:∀ i,0≤B i)(H:∀ i k, ‖f i k‖≤ B k) (p:ℕ) :
    ∀ᶠ δ:ℝ in 𝓝[>] 0,∀ i (z y:ℂ), ‖z‖ ≤ δ→‖y‖≤δ→ ‖operation p z (f i) - operation p y (f i)‖ ≤
      (1+B 1)*‖z-y‖:=by
 let M(s:ℝ):= ∑ i ∈ Finset.range p,(i+1:ℕ)*s^i*B (i+1)
 by_cases hp:p=0
 · subst p; exact Eventually.of_forall fun δ i z y hz hy=> by simp [operation,zero_le_one.trans (le_add_of_nonneg_right (hB 1)), mul_nonneg]
 have h : M 0 ≤ B 1:=by
   unfold M; rw [Finset.sum_eq_single 0]
   · simp
   exacts [fun i _ hi=>by simp [hi],fun h=> by simp [hp] at h]
 have hv: ∀ᶠ δ in 𝓝[>] 0, M δ ≤ 1+B 1:= ((show Continuous M from by unfold M; fun_prop).continuousWithinAt.tendsto.eventually_lt_const (show M 0 < 1+B 1 by linarith)).mono (fun _ hi=> hi.le)
 filter_upwards [hv,self_mem_nhdsWithin] with δ hδ (ht:0<δ) i z y hz hy
 unfold operation; rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']; simp only [pow_zero, sub_self, add_zero]
 refine (norm_sum_le ..).trans ((le_trans ?_ (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))))
 unfold M; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun j _=>?_)
 rw [← sub_smul,norm_smul]; exact (mul_le_mul (power_cost z y hz hy j) (H i _) (norm_nonneg _) (by positivity)).trans_eq (by ring)
lemma universal {x:ℝ} (h:0≤x) (hx:∀ i, ‖f i 1‖≤x) (H:Feasible f (fun _=>0))(p:ℕ) :
    ∀ᶠ δ:ℝ in 𝓝[>] 0,∀ i (z y:ℂ), ‖z‖ ≤ δ→‖y‖≤δ→ ‖operation p z (f i) - operation p y (f i)‖ ≤
      (1+x)*‖z-y‖:=by
 have hp k:∃ C:ℝ, 0≤C ∧ ∀ i, ‖f i k‖ ≤ C:= by obtain ⟨C,hC,p,h⟩:= H k; exact ⟨C,hC,fun i=>by simpa using h i⟩
 choose B hB hv using hp
 exact Eq.mp (by rw [if_pos rfl]) (worldwide (B:=fun k=> if k=1 then x else B k) (fun k=> by split_ifs <;> first| exact h| exact hB k)
    (f:=f) (fun i k=>by split; subst k; exact hx i; exact hv k i) p)
end YM.FVA2.GradedFar.Cart
