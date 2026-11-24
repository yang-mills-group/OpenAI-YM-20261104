import YM.Extension.UV.Holo
import Mathlib.Analysis.Complex.Schwarz

/-!
# From a polynomial-scale crude holomorphic envelope and a smaller real table bound.

Quantitative Newton divided differences on a single scalar parameter line, Banach-valued
codomain. Suppose all values have price `b^K` times real cap on a wide disk of radius H,
a real center plus k neighboring sample points at spacing s have the improved cap, and need an
analytic continuation at aperture r. The loss in cap at radius r is small as soon as r/s→0
and `b^K*(s/H)^k→0`, with k fixed ahead of delays (so this does not require a sector proof
of e.g. the same Taylor cancellations that produced the real cap). Input table and all
contours still have to carry the *same formulas*. We apply it to analytic recursions by choosing
s strictly intermediate between H and r; this is only the analytic interpolation substep
of vacuum and source estimates, no assumed receipt here treated as a physical theorem.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Frontier.Tuning.Thick
open Metric Function Filter Set
open scoped Topology Classical
variable {E: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def low (C:ℝ) (k:ℕ) := (1+2*C)^k
def high (C:ℝ) (k:ℕ) := (max 1 C)^k * (4:ℝ)^(k*k)
lemma low_zero C : low C 0=1:=pow_zero _
lemma high_zero C : high C 0=1:=by simp [high]
lemma low_one {C:ℝ} (hC:0≤C)(k:ℕ): (1:ℝ) ≤ low C k:=by apply one_le_pow₀ (by linarith:1≤1+2*C)
lemma low_go (C:ℝ) (k:ℕ): low C (k+1)=(1+2*C)*low C k:=pow_succ' ..
lemma high_pos (C:ℝ)(k:ℕ): 0≤high C k:=by unfold high; have h := le_max_left (1:ℝ) C; positivity
lemma high_go {C:ℝ} (hC:0≤C) (k:ℕ): C * high C k * 4^(k+1) ≤ high C (k+1):=by
   unfold high; rw [pow_succ' (max 1 C) k]; calc
      _ ≤ max 1 C*(max 1 C)^k * ((4:ℝ)^(k*k)*4^(k+1)) := by
          rw [show C * (max 1 C ^ k * (4:ℝ) ^ (k*k)) * 4^(k+1) = C*max 1 C ^k*((4:ℝ)^(k*k)*4^(k+1)) from by ring]; gcongr; exact le_max_right ..
      _ ≤ _ := by rw [← pow_add]; gcongr; norm_num; exact (show k*k+(k+1) ≤ (k+1)*(k+1) by nlinarith)

lemma slope_budget {f : ℂ→E} {x a : ℂ}{s H M:ℝ}(hs:0 < s)(hH:0 < H)
   (hn : DifferentiableOn ℂ f (ball x H)) (hb : ∀ y∈ ball x H, ‖f y‖ ≤ M) (hx : dist a x ≤ H/4) :
    (let g := fun z=> (s:ℂ) • dslope f a z
     DifferentiableOn ℂ g (ball x (H/4)) ∧ ∀ y∈ball x (H/4),‖g y‖ ≤ 4*(s/H)*M):= by
   intro g
   have he : ball a (H/2) ⊆ ball x H:= ball_subset_ball' (by linarith)
   have hm : a∈ball a (H/2):= mem_ball_self (by linarith)
   refine ⟨((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (he hm))).2 hn).mono (ball_subset_ball (by linarith))|>.const_smul _,fun y hy=>?_⟩
   have hp : MapsTo f (ball a (H/2)) (closedBall (f a) (2*M)):= fun y hY=> by
     simp only [mem_closedBall,dist_eq_norm]; exact (norm_sub_le ..).trans (by linarith only [hb _ (he hY),hb _ (he hm)])
   have hz : y∈ball a (H/2):= by refine ball_subset_ball' (by rw [dist_comm]; linarith) hy
   have h := Complex.norm_dslope_le_div_of_mapsTo_ball (hn.mono he) hp hz
   change ‖(s:ℂ) • dslope f a y‖ ≤ _
   rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.le]; apply (mul_le_mul_of_nonneg_left h hs.le).trans_eq (by field_simp; ring)
variable {f : ℂ → E} {a : ℕ→ ℂ} {x z : ℂ} {A C H M r s:ℝ}

lemma nodes (k:ℕ) (hs : 0<s) (hsH : s≤H/4^k) (hA:0≤A)(hC:0≤C)(hM:0≤M)
    (hz : dist z x < H/4^k) (hN: DifferentiableOn ℂ f (ball x H)) (hb : ∀ y∈ball x H, ‖f y‖ ≤ M)
    (ha : ∀ i<k, dist (a i) x ≤ H/4^k) (hc : ∀ i<k,dist z (a i) ≤ C*s) (hr : ∀ i<k,‖f (a i)‖ ≤ A)
    (hS : ∀ i j, i<j → j<k → s ≤ dist (a j) (a i)) : ‖f z‖ ≤ low C k*A+(high C k*(s/H)^k)*M:=by
 induction k generalizing a f H M A with
 | zero => simpa [high,low] using ((hb _ (by simpa using hz)).trans (le_add_of_nonneg_left (show 0 ≤ 1*A by linarith)))
 | succ k ih =>
   have hHa : 0<H := by_contra fun e=> lt_irrefl (dist z x) (hz.trans_le (by have := (show 0≤dist z x from dist_nonneg); exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt e) (by positivity)).trans (dist_nonneg)))
   have hdiv : H/4^(k+1)=(H/4)/4^k:= by rw [div_div,pow_succ']
   rw [hdiv] at ha hz hsH
   have hs':=slope_budget (s:=s) hs hHa hN hb ((ha 0 (Nat.zero_lt_succ k)).trans (div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))))
   let g:=fun z=> (s:ℂ) • dslope f (a 0) z
   have hp (i:ℕ)(hi:i<k): ‖g (a (i+1))‖ ≤ 2*A:=by
      have hy := hS 0 (i+1) (by omega) (by omega); have hd := hs.trans_le hy
      have hd' : a (i+1) ≠ a 0:= by intro he; rw [he,dist_self] at hd; exact (lt_irrefl _ hd).elim
      unfold g; rw [dslope_of_ne _ hd',slope_def_module, norm_smul,norm_smul, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.le,norm_inv,← dist_eq_norm,← mul_assoc,← div_eq_mul_inv]
      exact (mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hd).mpr hy)).trans ((norm_sub_le ..).trans (by linarith only [hr (i+1) (show i+1 < k+1 by omega),hr 0 (Nat.succ_pos k)]))
   have he:= ih (a:=fun i=>a (i+1)) (f:=g) (H:=H/4) hsH (by positivity : 0≤2*A) (by positivity) hz hs'.1 hs'.2 (fun i h=>ha _ (by omega)) (fun i h=> hc _ (by omega)) hp (fun i j hij hj=>hS _ _ (by omega) (by omega))
   have hv := hc 0 (Nat.succ_pos k)
   calc
    _ ≤ ‖f (a 0)‖+‖(z-a 0) • dslope f (a 0) z‖ :=by rw [sub_smul_dslope]; simpa only [add_sub_cancel] using (norm_add_le (f (a 0)) (f z-f (a 0)))
    _ ≤ A+ dist z (a 0)/s * ‖g z‖ := by dsimp only [g]; rw [norm_smul,norm_smul,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hs.le, ← mul_assoc, div_mul_cancel₀ _ hs.ne',← dist_eq_norm]; gcongr; exact hr _ (Nat.succ_pos _)
    _ ≤ A + C * (low C k * (2*A)+ (high C k*(s/(H/4))^k) * (4*(s/H)*M)):= add_le_add le_rfl (mul_le_mul ((div_le_iff₀ hs).mpr hv) he (norm_nonneg _) hC)
    _ ≤ low C (k+1)*A + high C (k+1)*(s/H)^(k+1)*M:=by
       rw [show s/(H/4)=4*(s/H) by ring,mul_pow]; rw [show A+C*(low C k*(2*A)+high C k*(4^k*(s/H)^k) * (4*(s/H)*M))=(1+2*C*low C k)*A+(C*high C k*4^(k+1))*((s/H)^(k+1)*M) by ring]
       rw [mul_assoc (high ..) _ M]
       apply add_le_add
       · rw [low_go]; exact mul_le_mul_of_nonneg_right (by linarith only [low_one hC k]) hA
       exact mul_le_mul_of_nonneg_right (high_go hC k) (by positivity)


/-- Estimate at and near the real center. The `low` term can be paid by very small r/s chosen
after k; high suppressed by at least k powers of s/H. k needn't be huge if the crude bound and
separation of exponents are fixed before delays. -/
lemma needle (k:ℕ) (hs : 0<s) (hsH : (k+1:ℕ)*s≤H/4^(k+1)) (hA:0≤A)(hM:0≤M)
    (hz : dist z x < H/4^(k+1)) (hr : 0≤ r)(hr' : r ≤ s)(hz': dist z x ≤ r)
    (hN: DifferentiableOn ℂ f (ball x H)) (hb : ∀ y∈ball x H, ‖f y‖ ≤ M)
    (hp' : ∀ i:ℕ,i ≤ k → ‖f (x+(i:ℂ)*s)‖ ≤ A):
    ‖f z‖ ≤ A+(r/s)*(low (k+1) k*(2*A)+(high (k+1) k*(4*(s/H))^k)*M) :=by
   have hH : 0<H:= by
         by_contra he; have hp : H/4^(k+1)≤0:= div_nonpos_of_nonpos_of_nonneg (le_of_not_gt he) (by positivity); linarith [show 0≤dist z x from dist_nonneg]
   have h:= slope_budget (a:=x) hs hH hN hb (by rw [_root_.dist_self]; linarith)
   let a (i:ℕ):ℂ := x+(i:ℂ)*s
   have hc i : dist (a i) x=i*s:=by simp [a,Complex.dist_eq, abs_of_nonneg hs.le]
   have hv i j (hi:i≤j): dist (a j) (a i)=(j-i:ℕ)*s := by
     rw [dist_eq_norm]; unfold a; rw [add_sub_add_left_eq_sub,← sub_mul,norm_mul,Complex.norm_real (r:=s), Real.norm_eq_abs,abs_of_nonneg hs.le]
     rw [Nat.cast_sub hi]
     have he' : ((j:ℂ)-(i:ℂ))=Complex.ofReal ((j:ℝ)-(i:ℝ)):= by norm_cast
     rw [he', Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ j-i by omega))]
   have hK : s≤ H/4^(k+1) := le_trans (le_mul_of_one_le_left hs.le (by exact_mod_cast k.zero_lt_succ)) hsH
   have he : s/(H/4) ≤ 1:=by rw [div_le_one (by positivity)]; exact hK.trans (div_le_div_of_nonneg_left hH.le (by norm_num) (by nlinarith [show (1:ℝ) ≤ 4^k from one_le_pow₀ (by norm_num), show (4:ℝ)^(k+1)=4^k*4 from by ring]))
   have h' (i:ℕ) (hi:i<k): ‖(s:ℂ) • dslope f x (a (i+1))‖ ≤ 2*A:=by
     rw [dslope_of_ne,_root_.slope_def_module, norm_smul,norm_smul,norm_inv,← dist_eq_norm,hc,Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hs.le]
     · apply ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hp' _ (by omega)) (by simpa using hp' 0 (Nat.zero_le _)))) (by positivity)) hs.le)).trans
       rw [← mul_assoc,two_mul]; apply mul_le_of_le_one_left (by linarith); apply le_trans (mul_le_mul_of_nonneg_left (show ((↑(i+1:ℕ)*s)⁻¹:ℝ)≤ s⁻¹ by gcongr; apply le_mul_of_one_le_left hs.le; exact_mod_cast Nat.le_add_left 1 i) hs.le) (mul_inv_cancel₀ hs.ne').le -- lhs A+A
     · have he:0< dist (a (i+1)) x:=by rw [hc]; positivity
       exact dist_pos.mp he
   have hh i (hi:i<k): dist z (a (i+1)) ≤ (k+1:ℕ)*s:= by
     push_cast
     apply (dist_triangle z x _).trans
     rw [dist_comm x, (hc (i+1))]; exact (add_le_add (hz'.trans hr') (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hs.le)).trans_eq (by ring)
   have hK' := nodes (a:=fun i=>a (i+1)) (z:=z) k hs (H:=H/4) (by rw [div_div,← pow_succ']; exact hK) (by linarith:0≤2*A) (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (M:=M) hM (by rw [div_div,← pow_succ']; exact hz) h.1 (fun y hy=>(h.2 y hy).trans (le_trans (mul_le_mul_of_nonneg_right (show 4*(s/H)≤1 by exact (le_of_eq (by ring : 4*(s/H)=s/(H/4))).trans he) hM) (by rw [one_mul]))) (fun i hi=>by rw [(hc _),div_div, ← pow_succ']; exact le_trans (by push_cast; gcongr : _ ≤ (k+1:ℕ)*s) hsH) (fun i h=>by simpa only [Nat.cast_add,Nat.cast_one] using hh i h) h' (fun i j hi hj=>by rw [hv _ _ (by omega)]; apply le_mul_of_one_le_left hs.le; exact_mod_cast (show 1 ≤ j+1-(i+1) by omega))
   rw [show s / (H/4)=4*(s/H) by ring,norm_smul,Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le] at hK'
   trans A + dist z x*‖dslope f x z‖
   · rw [dist_eq_norm,← norm_smul,sub_smul_dslope]; have h0:= norm_add_le (f x) (f z-f x); rw [add_sub_cancel] at h0
     exact h0.trans (add_le_add_left (by simpa using (hp' 0 (Nat.zero_le _))) _)
   apply add_le_add_right
   calc
     _ ≤ r*‖dslope f x z‖ := mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
     _ ≤ _ := by nth_rw 1 [(div_mul_cancel₀ r hs.ne').symm]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hK' (by positivity)
end YM.Frontier.Tuning.Thick
