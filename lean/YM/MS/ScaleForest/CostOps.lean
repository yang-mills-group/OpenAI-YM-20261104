import YM.MS.ScaleForest.Waves
/-!
# Relative-scale multi-pin forest budgets

Gain arbitrarily many powers at a between-pin join. Exponential taper
is the only length cost at a loop in this worst-case estimate. We will
use this class with IR growth powers at positive lengths and proving UV convergence at fixed
IR with *uniform* angular z limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {K : LineRule G} {X Y : Curtain G I} {p q : ℤ}
   {R a b c d S x y : ℝ} {A:I→QP}

-- closedBall subset for Enough.
theorem Enough.stops (h : Enough R) : closedBall (0:ℂ) R ⊆ Town := by
   intro i hi; obtain hm:= (mem_closedBall_zero_iff.mp hi).trans h.2; change 0< 2*i.re+1; linarith [Complex.abs_re_le_norm i, neg_abs_le i.re]

theorem Enough.feeLeg (h : Enough R) (μ:ℝ) (z:J→disc R) (s:J→ℝ) : scaleC 0 (fun i=> levy (-2*R) (-2*R) (s i)) (fun i=> ‖tenorK (z i) (μ+s i)‖) := by
   let T:= closedBall (0:ℂ) R
   have ht : DifferentiableOn ℂ (fun i:ℂ=> tenorK i μ) T:= fun i hi=> (holFee h.stops μ i hi).differentiableWithinAt
   obtain ⟨p,hp,he⟩:= IsCompact.exists_isMaxOn (isCompact_closedBall (0:ℂ) R) ⟨0,mem_closedBall_self h.1.le⟩ ht.continuousOn.norm; let V:= 1+‖tenorK p μ‖; have hV:0<V:= by unfold V; positivity
   refine ⟨ V,hV,0,fun i u hu=>?_⟩; rw [pow_zero,mul_one]; dsimp only; rw [μ_shift, norm_mul]; have hα : ‖tenorK (z i) μ‖ ≤ V:= by unfold V; exact le_trans ( he (Metric.ball_subset_closedBall (z i).property)) (le_add_of_nonneg_left zero_le_one)
   refine mul_le_mul hα ?_ (norm_nonneg _) hV.le; let α:ℂ:= z i; have hh:= (Complex.abs_re_le_norm (z i).val).trans (mem_ball_zero_iff.mp (z i).property).le; obtain ⟨he,hE⟩:= abs_le.mp hh -- re
   rw [amount, Complex.norm_exp]; rcases le_total (s i) 0 with hI|hI <;> [rw [ulev _ _ hI]; rw [ilev _ _ hI]] <;> apply exp_monotone <;> simp <;> nlinarith

variable (K) (hR : Enough R) (hX : Envelope R a b X) (hY : Envelope R c d Y) (hx : Waves R p X) (hy : Waves R q Y) (μ:ℝ)

include hX hx hR

theorem wrapU : Envelope R (a+ -2*R) (b+ -2*R) (Ufor K μ X) := by
   intro J q s v; let V i:= X (q i) (s i) (v i); unfold OnTest; unfold Ufor
   obtain h0 := costClose (n:=1) (K.ok.forms false) (fun i : J=> hx.token (q i) (q i).property (s i) (v i)) (hX J q s v)
     (fun i=> hR.town (q i).property) (fun i=> (hR.norm (q i).property).trans (by norm_num)) (hR.feeLeg μ q s)
   convert! h0 using 1; funext i; rw [Pi.mul_apply,levy_mul]; ring_nf
omit hx hR
include hY
omit [TopologicalSpace I] in
theorem wrapB : Envelope R (a+c) (b+d) (Bfor K X Y):= by
   intro J q s v; unfold OnTest Bfor; simp_rw [bridgeG_eq K.ok.rev]; convert! for_tree (hX J q s v) (hY J q s v) (u:=fun _=> K.half)
     (fun i j l=> railto (transport (K.ok.forms false).price i j l)) (fun _=>zero_le_one) using 1; funext i; rw [ Pi.one_apply,one_mul,levy_mul]

omit hX hY

structure AdmittedGap (A:I→QP) : Prop where
   sails: Continuous A
   walls: ∃ C:ℝ, 0<C∧∀ i:I, ‖A i‖ ≤ C
   lower: ∃ C:ℝ, 0<C∧∀ i:I, C ≤ ‖A i‖
variable (he : AdmittedGap A)
include he

theorem outGap (v:J→I)(s:J→ℝ)(hp:∀ i,s i≤0): Outpost (fun i=> exp (-s i) • A (v i)) (fun i=>exp (s i)) where
   pos i:= exp_pos _
   scala i:= exp_le_one_iff.mpr (hp i)
   payHigh:= by obtain ⟨C,hC,hP⟩:= he.walls; refine ⟨ C,hC,fun i=>?_⟩; rw [norm_smul_of_nonneg (exp_pos _|>.le), Real.exp_neg, ← div_eq_inv_mul]; gcongr; exact hP _
   payLow:= by obtain ⟨C,hC,hP⟩:= he.lower; refine ⟨ C,hC,fun i=>?_⟩; rw [norm_smul_of_nonneg (exp_pos _|>.le), Real.exp_neg, ← div_eq_inv_mul]; gcongr; exact hP _
include hX hY hR hx hy

-- extra UV gain, over small-z aperture
theorem wrapP (u:ℝ) : Envelope R u ((b+d)+-2*R) (Pfor K μ X Y A) := by
   obtain ⟨M,hM,hA⟩:= he.walls
   apply Envelope.paste
   · intro J q s v hQ; obtain ⟨n,hn⟩:= exists_nat_ge (u+2*R-a-c); let L:= K.half; obtain hK:= K.ok
     have hu i : 2*(q i :ℂ).re+1 ≤ ((2:ℕ):ℝ) := by obtain h:= hR.norm (q i).property; have hv:= Complex.re_le_norm (q i).val; norm_num; nlinarith
     have hr := pose (hk:=(hK.forms false).price) (hX J q s v) (hY J q s v) (outGap he v s hQ)
       (fun i : J=> hx.token _ (q i).property _ _) (fun i:J=> hy.token _ (q i).property _ _)
       (hK.forms false).token hK.rev hK.even (fun i :J=> hR.town (q i).property) hu (hR.feeLeg μ q s) n
     refine pay_price hr (b:=fun i=> exp (u*s i)) zero_lt_one (fun i=>?_); rw [ ulev _ _ (hQ i),ulev _ _ (hQ i),ulev _ _ (hQ i), ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,← Real.exp_add,one_mul ];
     apply exp_monotone; nlinarith [hQ i]
   intro J q s v hQ; let P:=fun i=> exp (-s i) • A (v i)
   have hp i: ‖P i‖≤ M:= by unfold P; rw [norm_smul_of_nonneg (exp_pos _|>.le)]; exact (mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.mpr (by have hh:= hQ i; linarith))).trans (hA _)
   obtain h := costPinn (n:=1) (P:=P) (K.ok.forms false) (fun i=> hx.token _ (q i).property (s i) (v i))
      (fun i=> hy.token _ (q i).property (s i) (v i)) (hX J q s v) (hY J q s v) (fun i=> hR.town (q i).property)
      (fun i=> (hR.norm (q i).property).trans (by norm_num)) (hR.feeLeg μ q s)
      (fun E _ _=> ⟨ M,hM,0,fun i p _=>by simpa only [ pow_zero, mul_one ] using hp i ⟩) K.ok.even K.ok.rev
   unfold OnTest Pfor; convert! h using 1; funext i; simp only [ Pi.mul_apply, ilev _ _ (hQ i), ←Real.exp_add]; ring_nf
end YM.MS.ScaleForest
