import YM.Work.G05.Taylor
import YM.Extra.WILSON_STARTUP.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Port
/-!
 # Auxiliary-box (Sienna) path towards real RG comparison – analytic orders quotes

 Use all requested derivative orders at once. Counting BRUSH measures
 Fréchet norm, crucial to give uniformly usable operator-norm estimates not
 assuming `Blob.Power` constants depend on internal counting spaces or gauge
 polls. Keep factorial conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Work.G05 WilsonStartup Function Filter Set MeasureTheory Metric
open Analysis Tensor Push ConnectedActivityE6 Blaze Brush
open PhysicalNext.Repeat Lantern
open scoped Classical BigOperators Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n j k : ℕ} {f g : E→F}{u C v : ℝ} {x : E}

abbrev PacketSeries (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] := (n : ℕ)→ Tensor.T E F n
variable {Q P: PacketSeries E F}
def through (n : ℕ) (P : PacketSeries E F) := ∑ j ∈ Finset.range (n+1), Tensor.diagonal (P j)
lemma daily (f : E→F): blockTaylor n f=through n (fun j=>Tensor.coeff f j 0):= rfl

def cap (Q : PacketSeries E F) (n : ℕ) (K: ℝ) : Prop := ∀ i≤n,‖Q i‖ ≤ K
private lemma coeff_fee (h:Brush n C 1 f x) (i:ℕ)(hi:i≤n): ‖coeff f i x‖≤ C := by
  unfold coeff; have hp: 1 ≤ (Nat.factorial i:ℝ):=by exact_mod_cast Nat.factorial_pos i
  rw [norm_smul,norm_inv,Real.norm_of_nonneg (zero_le_one.trans hp)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hp)).trans ((Brush.offer.1 h).2 i hi)
lemma capped (h:Brush n C 1 f x): cap (fun j=> coeff f j x) n C := coeff_fee h
private def constant (n : ℕ) : E→L[ℝ] (Fin n → E) := ContinuousLinearMap.pi (fun _=> ContinuousLinearMap.id ℝ E)
private lemma const_bounded (n : ℕ) : ‖constant (E:=E) n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u=> by rw [one_mul]; exact pi_norm_le_iff_of_nonneg (norm_nonneg u)|>.2 (fun _=>le_rfl)
lemma bound_diag (u : Tensor.T E F n) (x : E) (j : ℕ) : ‖iteratedFDeriv ℝ j (Tensor.diagonal u) x‖ ≤ n.descFactorial j * ‖u‖ * ‖x‖^(n-j):= by
   let H:=constant (E:=E) n
   change ‖iteratedFDeriv ℝ j (u ∘ H) x‖ ≤ _; rw [H.iteratedFDeriv_comp_right u.contDiff _ le_rfl]
   have h : ∏ _i:Fin j,‖H‖ ≤ 1 := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) (const_bounded _) 
   apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); apply (mul_le_of_le_one_right (norm_nonneg _) h).trans
   apply (u.norm_iteratedFDeriv_le j (H x)).trans; simp only [Fintype.card_fin]; apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) _ _) (by positivity)
   exact H.le_opNorm x|>.trans (mul_le_of_le_one_left (norm_nonneg _) (const_bounded _))

lemma tube_price (j : ℕ) (h : cap Q n C) (hx:‖x‖ ≤ 1) : Brush j (∑ i ∈ Finset.range (n+1), (∑ k∈Finset.range (j+1),(i.descFactorial k:ℝ))* C) 1 (through n Q) x := by
   let s (i k : ℕ):ℝ:= Nat.descFactorial i k; let p(i:ℕ):= (∑ k∈Finset.range (j+1),s i k)*C
   rw [show through n Q = (fun x => ∑ i∈Finset.range (n+1), Tensor.diagonal (Q i) x) from funext fun x=> Finset.sum_apply ..]
   refine Brush.spree _ (fun i=> Tensor.diagonal (Q i)) p zero_le_one (fun i hi=> ?_); apply Brush.offer.2; refine ⟨(diag_smooth ..).contDiffAt,fun k hk=>?_⟩
   have h' : i ≤ n:=Nat.le_of_lt_succ (Finset.mem_range.mp hi); have hC:0 ≤ C:=(norm_nonneg _).trans (h i h')
   apply le_trans (bound_diag (Q i) x k)
   apply le_trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hx)); exact mul_le_mul (Finset.single_le_sum (f:=s i) (fun k _=> Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))) (h i h') (norm_nonneg _) (Finset.sum_nonneg fun k _=> Nat.cast_nonneg _)

def overhead (n j:ℕ): ℝ := ∑ i∈Finset.range (n+1), ∑ k∈Finset.range (j+1),((i.descFactorial k):ℝ)
lemma gross (Q : PacketSeries E F) (h : cap Q n C) (hx:‖x‖ ≤ 1)(j): Brush j (overhead n j*C) 1 (through n Q) x := by rw [overhead, Finset.sum_mul]; exact tube_price j h hx

lemma through_priced (z : PacketSeries E F) (j:ℕ)(h:cap z n C)(hc:‖x‖≤1) : ‖through n z x‖≤ overhead n j*C:=(gross z h hc j).bound
@[fun_prop] lemma t_smooth (P:PacketSeries E F): ContDiff ℝ ω (through n P):= by
  rw [show through n P=(fun x => ∑ i∈Finset.range (n+1), Tensor.diagonal (P i) x) from funext fun x=> Finset.sum_apply ..]; exact ContDiff.sum fun i _=> Tensor.diag_smooth ..

lemma through_diff (P Q:PacketSeries E F) (i : ℕ): through i (P-Q)=through i P-through i Q:= by
  ext1 x
  simp only [Pi.sub_apply,through, Finset.sum_apply, Tensor.diagonal, _root_.sub_apply, Finset.sum_sub_distrib]

-- `Startup.bound` needs Analytic extension from a fleeting receipt. Local version on open ball.
lemma flat_price (h: FlatAt n f 0) (hu: Brush n C 1 f x) (H:∀ y∈ Metric.ball 0 u, Brush n C 1 f y) (hx:‖x‖<u) (j:ℕ)(hj : j ≤ n):
    ‖iteratedFDeriv ℝ j f x‖ ≤ C*‖x‖^(n-j) := by
  have ht:0 < u := (norm_nonneg x).trans_lt hx
  have hp :=hu.nonneg
  clear ht hu
  induction hj using Nat.decreasingInduction generalizing x with
  | self=> simpa only [Nat.sub_self,pow_zero,mul_one] using (Brush.offer.1 (H x (mem_ball_zero_iff.mpr hx))).2 n le_rfl
  | of_succ i hi ih =>
    let K := iteratedFDeriv ℝ i f
    let D:= closedBall (0:E) ‖x‖
    have he:{y| y ∈ D} ⊆ ball (0:E) u := fun _ hy=> mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy) hx)
    have hg : ‖K x - K 0‖≤ C*‖x‖^(n-(i+1))*‖x-0‖ := (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy=> (H y (he hy)).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast hi)) (fun y hy=> Eq.trans_le norm_fderiv_iteratedFDeriv ((ih (mem_ball_zero_iff.mp (he hy))).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hy) _) hp))) (mem_closedBall_self (norm_nonneg x)) (mem_closedBall_zero_iff.mpr le_rfl)
    rw [sub_zero,show K 0=0 from h i hi,sub_zero] at hg
    rw [show n-i = n-(i+1)+1 by omega,pow_succ,← mul_assoc]; exact hg

lemma grade_price (h:FlatAt n f 0)(H: ∀ x∈ ball (0:E) u, Brush j C 1 f x) (hN:n ≤ j)(hx:‖x‖ < u) (hu:u≤1) : Brush j (C * u^n) u⁻¹ f x := by
  let q:=H x (mem_ball_zero_iff.mpr hx); have hw:0<u:= (norm_nonneg _).trans_lt hx
  refine ⟨q.smooth,by positivity,fun i hi => ?_⟩
  rw [mul_assoc,inv_pow,← div_eq_mul_inv]
  by_cases hv:i≤n
  · apply le_trans (flat_price h (q.smaller hN) (fun x hx=> (H x hx).smaller hN) hx i hv); apply mul_le_mul_of_nonneg_left _ q.nonneg
    apply le_trans (pow_le_pow_left₀ (norm_nonneg _) hx.le _); apply le_of_eq; rw [eq_div_iff (pow_pos hw i).ne', ← pow_add, Nat.sub_add_cancel hv]
  apply le_trans ((Brush.offer.1 q).2 i hi); exact le_mul_of_one_le_right q.nonneg ((one_le_div (pow_pos hw i)).2 (pow_le_pow_of_le_one hw.le hu (by omega))) -- fix

lemma overall (H:∀ x∈ ball (0:E) u, Brush k C 1 f x) (hu:u≤1)(hi : n+1 ≤ k) (hx:‖x‖<u) :
    Brush k ((C+overhead n k*C)*u^(n+1)) u⁻¹ (f - blockTaylor n f) x:=by
  have ht:0 < u:= (norm_nonneg _).trans_lt hx
  have hh:= H 0 (mem_ball_self ht)|>.smaller (show n≤k by omega)
  exact grade_price (flat_sub_taylor f n hh.smooth) (fun x hx=> (H _ hx).separating (gross (fun i=>Tensor.coeff f i 0) (capped hh) ((mem_ball_zero_iff.mp hx).le.trans hu) _)) hi hx hu
end YM.Juniper.LocalAtlas
