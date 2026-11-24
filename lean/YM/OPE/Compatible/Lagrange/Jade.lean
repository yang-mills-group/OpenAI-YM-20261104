import YM.OPE.Compatible.Lagrange.Shine
/-!
# Near central address has bounded individual coefficients
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Filter Metric Polynomial Finset Complex
open scoped BigOperators Topology
variable {R a b : ℝ} {m : ℕ} {i:ℤ}
-- step a positive, x0=b within half

def pin (a b:ℝ)(i:ℤ):ℂ:= (((i:ℝ)*a + b:ℝ):ℂ)
def slice (m:ℕ):= Icc (-(m:ℤ)) (m:ℤ)
lemma admits_zero (m:ℕ) : 0∈ slice m:=by simp [slice]
lemma slice_step (m:ℕ): slice (m+1)= insert (-((m+1:ℕ):ℤ)) (insert ((m+1:ℕ):ℤ) (slice m)):=by ext i; simp only [slice,mem_Icc,mem_insert,Nat.cast_add,Nat.cast_one]; omega
lemma pin_diff (a b:ℝ)(i j:ℤ):‖pin a b i-pin a b j‖= |a| * |(i:ℝ)-j|:=by
   unfold pin; rw [← ofReal_sub,norm_real]; simp only [Real.norm_eq_abs,add_sub_add_right_eq_sub]; rw [← sub_mul,abs_mul,mul_comm]
local notation "v" => pin a b
private lemma weight (ha:0<a)(hi: (i+1)∈slice m)(hp:0 ≤ i) : ‖Lagrange.nodalWeight (slice m) v (i+1)‖ ≤ ‖Lagrange.nodalWeight (slice m) v i‖:=by
    let u:ℤ:= m; have ht : -(m:ℤ) ≤ i+1 ∧ i+1 ≤ m:= mem_Icc.mp hi
    have hz : -u∈ (slice m).erase (i+1):=by simp only [mem_erase,u,slice,mem_Icc]; omega
    have hf : u ∈ (slice m).erase i :=by simp only [mem_erase,u,slice,mem_Icc]; omega
    let f (i j:ℤ):= ‖(v i - v j)⁻¹‖; let z:=(slice m).erase i; let y:=(slice m).erase (i+1)
    have hφ: (∏ j∈ z.erase u, f i j) = ∏ j∈ y.erase (-u), f (i+1) j:= by
       refine prod_bij' (fun j _=>j+1) (fun j _=> j-1) (fun j h=>?_) (fun j h=>?_) (fun j _=>by omega) (fun j _=>by omega) (fun j _=>?_)
       · simp only [z,u,slice,y,mem_Icc,mem_erase] at *; omega
       · simp only [z,u,slice,y,mem_Icc,mem_erase] at *; omega
       unfold f; simp [norm_inv,pin_diff]
    unfold Lagrange.nodalWeight; rw [norm_prod,norm_prod]; change (∏ j∈y,f (i+1) j) ≤ ∏ j∈ z,f i j
    rw [← mul_prod_erase _ _ hz, ← mul_prod_erase _ _ hf,hφ]; refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun _ _=>norm_nonneg _)
    have h: (i:ℝ) < u:=by exact_mod_cast (show i< (m:ℤ) by omega)
    have hh : 0 ≤ (i:ℝ):=by exact_mod_cast hp
    unfold f; rw [norm_inv,norm_inv,pin_diff,pin_diff, abs_of_pos ha,abs_of_neg (sub_neg.mpr h)]; push_cast; refine inv_anti₀ (by nlinarith only [h,ha,mul_pos ha (neg_pos.mpr (sub_neg.mpr h))]) (mul_le_mul_of_nonneg_left ?_ ha.le); rw [abs_of_nonneg]; all_goals linarith
private lemma weigh (m:ℕ)(a b:ℝ)(i:ℤ):‖Lagrange.nodalWeight (slice m) (pin a b) (-i)‖=‖Lagrange.nodalWeight (slice m) (pin a b) i‖:=by
    simp only [Lagrange.nodalWeight,norm_prod,norm_inv,pin_diff]; refine prod_bij' (fun j _=>-j) (fun j _=>-j) (fun j h=>?_) (fun j h=>?_) (fun j _=>neg_neg _) (fun j _=>neg_neg _) (fun j _=>?_)
    · simp only [slice,mem_erase,mem_Icc] at *; omega
    · simp only [slice,mem_erase,mem_Icc] at *; omega
    push_cast; rw [show (-(i:ℝ)-j)= - ((i:ℝ) - -j) from by ring,abs_neg]
lemma weight_zero (ha:0<a)(hi:i∈ slice m): ‖Lagrange.nodalWeight (slice m) v i‖ ≤ ‖Lagrange.nodalWeight (slice m) v 0‖:=by
   have he : ∀ (j:ℕ), j ≤ m → ‖Lagrange.nodalWeight (slice m) v j‖ ≤ ‖Lagrange.nodalWeight (slice m) v 0‖:=by
       intro j h; induction j with
       | zero => simp
       | succ j ih=> rw [Nat.cast_add,Nat.cast_one]; have hv:(j:ℤ)+1∈ slice m:=by simp only [slice,mem_Icc]; omega
                     exact (weight ha hv (by omega)).trans (ih (by omega))
   simp only [slice,mem_Icc] at hi; rcases le_total 0 i with h|h
   · simpa [Int.toNat_of_nonneg h] using he i.toNat (by omega)
   rw [← weigh m]; simpa [Int.toNat_of_nonneg (neg_nonneg.mpr h)] using he (-i).toNat (by omega)
lemma never_less (ha:0<a)(hb:0<b)(hp:b ≤ a/2)(i:ℤ): ‖pin a b 0‖ ≤ ‖pin a b i‖:=by
   simp only [pin,Int.cast_zero,zero_mul,zero_add,norm_real,Real.norm_of_nonneg hb.le,Real.norm_eq_abs]; by_cases h:(0:ℤ) ≤ i
   · exact (le_add_of_nonneg_left (mul_nonneg (by exact_mod_cast h) ha.le)).trans (le_abs_self _)
   have hv:(i:ℝ)≤ -1 :=by exact_mod_cast (show i ≤ -1 by omega)
   rw [abs_of_nonpos]; all_goals nlinarith only [mul_le_mul_of_nonneg_right hv ha.le,hp,ha]
lemma pin_zero_pos (a : ℝ) (h:0<b): 0< ‖pin a b 0‖:=by simp [pin,h.ne']
lemma never_zero (ha:0<a)(hb:0<b)(hp:b≤a/2)(i:ℤ): pin a b i≠ 0:= norm_pos_iff.mp ((pin_zero_pos _ hb).trans_le (never_less ha hb hp i))
lemma central (ha:0<a)(hb:0<b)(hp:b≤a/2)(i:ℤ)(hi:i∈slice m): ‖eval 0 (Lagrange.basis (slice m) v i)‖ ≤ ‖eval 0 (Lagrange.basis (slice m) v 0)‖:=by
   rw [Lagrange.eval_basis_not_at_node hi (Ne.symm (never_zero ha hb hp i)), Lagrange.eval_basis_not_at_node (admits_zero _) (Ne.symm (never_zero ha hb hp 0))]; simp only [norm_mul,norm_inv,zero_sub,norm_neg]; exact mul_le_mul_of_nonneg_left (mul_le_mul (weight_zero ha hi) (inv_anti₀ (pin_zero_pos a hb) (never_less ha hb hp i)) (by positivity) (norm_nonneg _)) (by positivity)
end YM.FrameRead
