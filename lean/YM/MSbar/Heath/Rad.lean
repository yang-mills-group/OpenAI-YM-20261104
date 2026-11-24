import YM.AnalyticBridge.VERIFIED_RESET_STEP.Rows
import YM.MergeProof.North.Broom
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter Set MeasureTheory
open Push
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{n:Side}{x y:Site n}
-- Dial explicit with floored lengths
open Finset
protected def wick (M:ℕ)(α:ℝ) (x y:Site n):=Real.exp (-α*(↑(separation x y / M):ℝ))
def meter (r:ℝ) := ∑' i:ℕ,(↑(i+1:ℕ):ℝ)^4*Real.exp (-r*i)
lemma charges {r:ℝ}(h:0<r): Summable (fun i:ℕ=> (↑(i+1:ℕ):ℝ)^4*Real.exp (-r*i)):=by
   let b:=Real.exp (-r); have he:‖b‖<1:=by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr h)
   let f i:=(↑(i:ℕ):ℝ)^4*b^i; have hf:Summable f := summable_pow_mul_geometric_of_norm_lt_one 4 he
   apply Summable.congr ((hf.comp_injective (show Injective fun i:ℕ=>i+1 from fun i j h=>add_right_cancel h)).mul_right b⁻¹); intro i; rw [Function.comp_apply]; rw [show f (i+1)=(↑(i+1:ℕ):ℝ)^4*(b^i*b) from (by unfold f; rw [pow_succ b]),mul_assoc,mul_inv_cancel_right₀ (Real.exp_pos _).ne']; unfold b; rw [← Real.exp_nat_mul,mul_comm (-r)] -- careful LHS comp
lemma meter_pos {r:ℝ}(h:0<r) : 0< meter r := lt_of_lt_of_le (by positivity : 0 < (↑(0+1:ℕ):ℝ)^4*Real.exp (-r*(↑(0:ℕ):ℝ))) ((charges h).le_tsum _ (fun i _=>by positivity)) -- binder
lemma horizon (M:ℕ)(x:Site n): (halo M {x}).card ≤ (2*M+1)^4:= (Corona.halo_size {x} M).trans (by simp [two_mul])
lemma wick_pays {r:ℝ}(h:0<r)(M:ℕ)(hk:0<M)(x: Site n): (∑ i:Site n, Heath.wick M r x i) ≤ (2*M+1:ℝ)^4*meter r:=by
    let J(i:Site n):= separation x i/M; let s:= Finset.univ.image J
    let f(k:ℕ):=univ.filter (fun i=>J i=k); let g(k:ℕ):ℝ:= Real.exp (-r*k); let w(i):= Heath.wick M r x i
    have he j: ((f j).card:ℝ) ≤ (2*M+1:ℝ)^4*(↑(j+1:ℕ):ℝ)^4:=by
       have ht : (f j).card ≤ (2*((j+1)*M)+1)^4:= le_trans (Finset.card_le_card ?_) (horizon ((j+1)*M) x)
       swap; · intro i hi; apply halo_spec.mpr; have hp : separation x i < (j+1)*M:= (Nat.div_lt_iff_lt_mul hk).1 (by rw [show separation x i/M=j from (mem_filter.mp hi).2]; omega); exact ⟨_, mem_singleton_self x,hp.le⟩
       exact le_trans (Nat.cast_le.mpr ht) (by push_cast; rw [← mul_pow]; gcongr; nlinarith [Nat.cast_nonneg (α:=ℝ) j, Nat.cast_nonneg (α:=ℝ) M])
    have hi : (∑ k∈s, (f k).card * g k)=∑ i : Site n,w i:=by
       calc
         _ = ∑ k∈s,∑ i∈f k,w i := by
               apply Finset.sum_congr rfl; intro k hk; rw [show ∑ i∈f k,w i=∑ i∈f k, g k from sum_congr rfl fun i hi=> (show g (J i)=_ from congr_arg _ ((mem_filter.mp hi).2))]; simp
         _ = _:= Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=s) (g:=J) (fun i hi=> Finset.mem_image_of_mem _ hi) _
    change ∑ i : Site n,w i ≤ _; rw [← hi]
    trans ∑ j∈s,(2*M+1:ℝ)^4*((↑(j+1:ℕ):ℝ)^4*g j)
    · apply sum_le_sum; intro j _; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he _) (Real.exp_pos _).le
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((charges h).sum_le_tsum _ (fun i _=> mul_nonneg (by positivity) (Real.exp_pos _).le)) (by positivity)
lemma radial (r:ℝ)(h:0<r)(x:Site n) : (∑ i:Site n, Real.exp (-r*separation x i)) ≤ 81*meter r:= by have hp:=wick_pays h 1 (by norm_num) x; norm_num [Heath.wick] at hp; simpa using hp
end YM.MSbar.Heath
