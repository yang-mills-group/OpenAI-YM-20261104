import YM.OPE.Compatible.Lark.Reins
/-!
# Absolute polynomial budgets. Measure on directed legs; no exponent demanded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff
variable {I J:Type*}{n m:Side}
namespace Script
open Page
variable (a:I→Site n) (b:J→Site n)
def Dux (k:ℕ)(x y: Site n):ℝ:= (1+(separation x y:ℝ))^k
def PaidT (k:ℕ)(Z:Matrix I J ℝ)(D:ℝ):Prop:=0 ≤ D∧ ∀ i j,Dux k (a i) (b j)* ‖Z i j‖≤ D
variable {a b}
lemma dux_nn (k:ℕ)(x y:Site n):0 ≤ Dux k x y:=by unfold Dux;positivity
lemma dux_le (k:ℕ)(x y z: Site n):Dux k x z≤Dux k x y * Dux k y z:=by
      unfold Dux; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity) _; have hh:(separation x z:ℝ) ≤ (separation x y:ℝ)+(separation y z:ℝ):=by exact_mod_cast separation_triangle x y z
      nlinarith [show 0 ≤ (separation x y:ℝ)*(separation y z:ℝ) by positivity]
variable {A B:Matrix I J ℝ}{k r:ℕ}{D V s:ℝ}
lemma PaidT.add (h:PaidT a b k A D)(he:PaidT a b k B V):PaidT a b k (A+B) (D+V) :=by
      refine ⟨add_nonneg h.1 he.1,fun i j=>?_⟩;rw [Matrix.add_apply]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (dux_nn ..)).trans; rw [mul_add]; exact add_le_add (h.2 i j) (he.2 i j)
lemma PaidT.neg (h: PaidT a b k A D): PaidT a b k (-A) D:=⟨h.1,fun i j=>by rw [Matrix.neg_apply,norm_neg];exact h.2 i j⟩
lemma PaidT.aug (h: PaidT a b k A D)(hp:D≤V):PaidT a b k A V:=⟨h.1.trans hp, fun i j=>(h.2 i j).trans hp⟩
lemma PaidT.links [Fintype J]{U:Type*} {R:Matrix J U ℝ}{c:U→Site n}(h:PaidT a b k A D)(hf:PaidT b c k R V):PaidT a c k (A*R) (Fintype.card J * (D*V)):=by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h.1 hf.1),fun i j=> ?_⟩
      rw [Matrix.mul_apply]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (dux_nn ..)).trans; rw [mul_sum]; apply (sum_le_sum (g:=fun _=>D*V) (fun w _=>?_)).trans_eq; · simp
      rw [norm_mul]; apply (mul_le_mul_of_nonneg_right (dux_le k (a i) (b w) (c j)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans; rw [mul_mul_mul_comm]; exact mul_le_mul (h.2 i w) (hf.2 w j) (mul_nonneg (dux_nn ..) (norm_nonneg _)) h.1
open Planned.PrimaryIntegral295.Carrier
lemma pay_field (A: Row I J)(h:A.strip s D)(hp:0<s)(i:Tab I n)(j:Tab J n):
   Dux k i.1 j.1 * ‖A.acts n i j‖ ≤ widthCost s k * D:=by
      let f(z:Cover):= if j.1=i.1+wrap n z then A i.2 j.2 z else 0; change _ * ‖∑' z,f z‖≤ _; have He : Summable f:= (show Summable (A i.2 j.2) from ((h i.2 j.2).unweighted hp.le).2.1.of_norm).indicator {z|j.1=i.1+wrap n z} |>.congr (fun z=> by by_cases h:j.1=i.1+wrap n z <;>simp_all only [f, Set.indicator, Set.mem_setOf_eq, if_false]); let q:=Dux k i.1 j.1
      refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm He.norm) (dux_nn ..)).trans ?_;rw [←tsum_mul_left]; have he := width_income hp (h i.2 j.2) k; apply ((He.norm.mul_left q).tsum_le_tsum ?_ he.2.1).trans he.2.2; intro z; unfold f; split
      next hh =>
         change q * _≤ ‖A i.2 j.2 z‖ * _; rw [mul_comm q]; suffices ht:q ≤ poise k z by rw [liftCostSame] at ht; exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
         unfold q poise Dux notch; rw [separation_comm,hh]; apply pow_le_pow_left₀ (by positivity); push_cast; gcongr; unfold separation; rw [add_sub_cancel_left]; exact within_size ..
      next hh=>simp only [norm_zero,mul_zero]; exact he.1 _
lemma roll_near (x:Site n)(p:Cover): separation (x+wrap n p) x ≤ size p:=by unfold separation; rw [add_sub_cancel_left]; exact within_size ..
variable [Fintype I]
lemma render_layers (i:Site n)(p q:Tab I n)(z:Page I (r+2))(x:Fin r→deck I n):
      Dux k p.1 q.1*‖render i z (Fin.cons (deltaH p) (Fin.cons (deltaH q) x))‖ ≤3^k * Page.figure k z * ∏ j,‖x j‖:=by
          have hp(i:Page I (r+2)):0≤figure k i:=zero_le_one.trans (payer k i)
          have hg:0 ≤ 3^k * Page.figure k z * ∏ j,‖x j‖:= mul_nonneg (mul_nonneg (by positivity) (hp z)) (prod_nonneg fun i _=> norm_nonneg _)
          simp_rw [renderer]; split_ifs with he ht
          · apply mul_le_mul _ _ (norm_nonneg _) (by have :=hp z; positivity); swap
            · unfold render; rw [norm_prod]; apply prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> norm_le_pi_norm ..)
            have hh : (1+ separation p.1 q.1: ℕ) ≤ 3*Page.stamp z:=by
                 have ha: p.1=i+wrap n (z 0).1:= congr_arg Prod.fst he; have hh: q.1= i+wrap n ((mort z 0).1):=congr_arg Prod.fst ht
                 have hy:= roll_near i ((z 0).1); have hx:= roll_near i (mort z 0).1; have h:= separation_triangle p.1 i q.1; rw [separation_comm i] at h; rw [ha,hh] at h -- recursive hazards
                 have h₁:size (z 0).1 ≤ stamp z:= z.primary_size; have h₂:size (mort z 0).1 ≤ stamp z:=(Page.primary_size ..).trans (notched z); have hb:1 ≤ stamp z:=notch_one _; rw [ha,hh];omega
            unfold Dux figure poise; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity);exact_mod_cast hh
          all_goals simp only [norm_zero,mul_zero]; exact hg
lemma lib_pay {k u:ℕ}(S:Script I (u+2))(p q:Tab I n)(x:Fin u→deck I n)(hs:soot k S D):
      Dux k p.1 q.1 * ‖library n S (Fin.cons (deltaH p) (Fin.cons (deltaH q) x))‖ ≤ n.val^4 * ((3:ℝ)^k* D*(∏ i,‖x i‖)):=by
          let C : Fin (u+2)→ deck I n:= Fin.cons (deltaH p) (Fin.cons (deltaH q) x); let T:= (∏ i, ‖x i‖); have ht:0≤T:=prod_nonneg fun i _=>norm_nonneg _; let K:= 3^k*D*T; let w:= Dux k p.1 q.1; have hv:0≤w:= dux_nn ..
          have he(i:Site n): w*‖scribe i S C‖≤K:=by
                unfold scribe; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (instruments S (sootS hs) i C).summable.norm) hv).trans; rw [←tsum_mul_left]; apply (((instruments S (sootS hs) i C).summable.norm.mul_left w).tsum_le_tsum ?_ (hs.2.1.mul_left (3^k*T))).trans
                · rw [tsum_mul_left]; unfold K;rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2.2 (by positivity)) ht
                intro j; rw [norm_mul,mul_left_comm]; apply (mul_le_mul_of_nonneg_left (render_layers i p q j x) (norm_nonneg _)).trans_eq; ring
          unfold library; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) hv).trans; rw [mul_sum]; apply (sum_le_sum (fun i _=>he i)).trans; rw [sum_const,card_univ,site_card,nsmul_eq_mul]; push_cast; exact le_rfl
end Script
end YM.OPE.Flume
