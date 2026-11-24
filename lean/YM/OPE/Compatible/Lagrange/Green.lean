import YM.OPE.Compatible.Lagrange.Jade
/-!
# Interpolate dot price only
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Filter Metric Polynomial Finset Complex
open scoped BigOperators Topology
variable {R a b A B t : ℝ}{f :ℂ→ℂ}{n m:ℕ}
local notation "v" => pin a b
private lemma norm_basis0 (ha:0<a)(hb:0<b)(hp:b ≤ a/2)(m:ℕ): ‖eval 0 (Lagrange.basis (slice m) v 0)‖ ≤ 1:=by
    have h(i:ℕ) : ‖eval 0 (Lagrange.basis (slice i) v 0)‖ = ∏ j∈ (slice i).erase 0, (‖v 0-v j‖⁻¹ * ‖v j‖):=by unfold Lagrange.basis; rw [eval_prod,norm_prod]; apply prod_congr rfl; intro j hj; simp [Lagrange.basisDivisor,norm_inv]
    induction m with
    | zero => simp [slice]
    | succ t ih =>
       rw [h (t+1)]; rw [h] at ih; let i:ℤ:= t+1; have he:0 < i :=by unfold i; omega
       rw [slice_step t,Nat.cast_add,Nat.cast_one]; change (∏ j∈ (insert (-i) (insert i (slice t))).erase 0,_) ≤ _; rw [erase_insert_of_ne (a:=-i) (b:=0) (by omega),erase_insert_of_ne (a:=i) (b:=0) (by omega), prod_insert (by simp only [mem_insert,mem_erase,slice,mem_Icc]; unfold i; omega),prod_insert (by simp only [mem_erase,slice,mem_Icc]; unfold i; omega),← mul_assoc]
       apply le_trans (b:=(1:ℝ)*1) (mul_le_mul _ ih (prod_nonneg fun _ _=>by positivity) zero_le_one) (by norm_num); have hi:(1:ℝ) ≤ i:=by exact_mod_cast he
       have hI:(0:ℝ) < i :=by linarith
       rw [pin_diff,pin_diff]; simp only [pin,Int.cast_zero,Int.cast_neg,sub_neg_eq_add,zero_add,zero_sub,abs_neg,abs_of_pos hI,abs_of_pos ha,norm_real,Real.norm_eq_abs]; rw [abs_of_nonpos (by nlinarith : -(i:ℝ)*a+b ≤ 0),abs_of_pos (by positivity: 0 < (i:ℝ)*a+b)]; field_simp; nlinarith only [sq_nonneg b]
lemma inject_pin (h:0<a)(b:ℝ) : Injective (pin a b):=by
   intro i j hi; unfold pin at hi; exact_mod_cast mul_right_cancel₀ h.ne' (add_right_cancel (ofReal_injective hi))
lemma fits_pin (h:0<a)(he:0<b)(hx:b≤a/2)(hf: (↑m+1:ℝ)*a≤ R/3): ∀ i∈slice m, ‖v i‖ ≤ R/3:=by
   intro i hi; have hh:=mem_Icc.1 hi; have ht:-(m:ℝ) ≤ i:= by exact_mod_cast hh.1; -- one statement per line
   have hg:(i:ℝ)≤m:=by exact_mod_cast hh.2
   rw [pin,norm_real,Real.norm_eq_abs,abs_le]; constructor <;> nlinarith only [he,hx,h,hf,mul_le_mul_of_nonneg_right ht h.le,mul_le_mul_of_nonneg_right hg h.le]
lemma dot_price (ht:0≤t)(h:0<a)(he:0<b)(hx:b≤a/2)(hR:0<R)(hf:(↑m+1:ℝ)*a≤ R/3) (hd:DifferentiableOn ℂ f (closedBall 0 R))(hp:∀ z:ℂ, ‖z‖=R→ ‖f z‖ ≤ A)(hw:∀ i∈slice m, t* ‖f (v i)‖ ≤ B): t* ‖f 0‖ ≤ t*A*(1/2:ℝ)^(slice m).card + (slice m).card*B :=by
   let l i:=eval 0 (Lagrange.basis (slice m) v i) * f (v i); let S:=∑ i∈slice m, l i; have hg : ‖f 0-S‖ ≤ _:=contour_value ⟨0,admits_zero _⟩ (inject_pin h b|>.injOn (s:=↑(slice m))) (fun i _=> never_zero h he hx i) hR (fits_pin h he hx hf) hd hp
   calc
       _ ≤ t*(‖f 0-S‖ + ‖S‖) := mul_le_mul_of_nonneg_left (by
           conv_lhs => rw [← sub_add_cancel (f 0) S]
           exact norm_add_le ..) ht
       _ ≤ t*(A*(1/2:ℝ)^(slice m).card) + t*‖S‖ :=by rw [mul_add]; exact add_le_add_left (mul_le_mul_of_nonneg_left hg ht) _
       _ ≤ _ := add_le_add (le_of_eq (by ring)) ?_
   refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) ht).trans ?_; rw [mul_sum]; refine le_trans (b:=∑ i∈slice m,B) (sum_le_sum fun i hi=>?_) (by simp); unfold l; rw [norm_mul]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((central h he hx _ hi).trans (norm_basis0 h he hx _)) (norm_nonneg _)) ht) ?_; rw [one_mul]; exact hw i hi
end YM.FrameRead
