import YM.OPE.Compatible.Grid.Bookie
/-!
# Taylor reading with moderate budget. Needed for arbitrary sizes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Page Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics PertExtension Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s b U D:ℝ}{d r m k q:ℕ}
variable {p:Script (Shade G) k}
open Set
lemma valueCharge (f:ℝ→ℝ)(hf: ContDiff ℝ ⊤ f)(t:ℝ)(ht:0<t)(k:ℕ)(C:ℝ)(hh:0≤C)(hp:∀ v:ℝ,‖iteratedDeriv (k+1) f v‖≤C):
    ‖f t- ∑ i∈range (k+1), t^i * WardBin.leading i f‖ ≤ C*t^(k+1):=by
         have he(i:ℕ)(x:ℝ)(hx:x∈Icc (0:ℝ) t): iteratedDerivWithin i f (Icc 0 t) x=iteratedDeriv i f x:=by rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) ((hf.of_le le_top).contDiffAt) hx,← iteratedDeriv_eq_iteratedFDeriv]
         have hg:= taylor_mean_remainder_bound (n:=k) (f:=f) ht.le ((hf.of_le le_top).contDiffOn) (right_mem_Icc.mpr ht.le) (C:=C) fun i hi=>by rw [he _ _ hi]; exact hp i
         have hz:taylorWithinEval f k (Icc 0 t) 0 t=∑ i∈range (k+1), t^i* WardBin.leading i f:=by rw [taylor_within_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [he _ 0 (left_mem_Icc.mpr ht.le),sub_zero]; simp only [smul_eq_mul,WardBin.leading]; ring
         rw [← hz]; rw [sub_zero] at hg; exact hg.trans ((div_le_iff₀ (by exact_mod_cast k.factorial_pos)).mpr (le_mul_of_one_le_right (by positivity) (by exact_mod_cast k.factorial_pos)))
lemma priceSpin (h: soot q p b)(he:2*(r+2)≤q)(U:ℝ)(hu:0 ≤ U): ∃ K:ℝ,0 ≤ K∧∀ v:fieldX (Shade G), Quiet v 0→(∀ i:Edge Cover,‖indexS i v‖≤ U)→∀ t:ℝ, 0 < t→
     ‖testQ p (lotU (t • v)) -∑ i∈range (r+3), t^i *wholeX (timbre ships p i) (fun _=>v)‖ ≤ K*t^(r+3):=by
         obtain ⟨C,hc,H⟩:= ozone G k U _ hu (lumenD G) (r+3); let f:ℕ:=2*k+3; let K:= C*(f:ℝ)^(r+3); have hk:0 ≤ K:=by unfold K; positivity
         refine ⟨b*K,mul_nonneg (Sack.coins h) hk,fun v hv ht t hx=>?_⟩
         let a(v':Page (Shade G) k)(t:ℝ):= verseX (ships v') (lotU (t • v)); let c(i:ℕ)(j:Page (Shade G) k):= t^i * p j * WardBin.leading i (a j)
         have hx(j): ‖a j t-∑ i∈range (r+3),t^i*WardBin.leading i (a j)‖≤ K*figure q j*t^(r+3):=by
              apply valueCharge _ (cash_smooth (ships j) v) t hx (r+2) _ (mul_nonneg hk (zero_le_one.trans (payer q _))); intro x; apply (H _ _ (theater _) (fun i _=>ht i) x).trans; unfold K; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hc; change (lawn (ships j)+ (1:ℝ))^(r+3)≤ _; apply le_trans (pow_le_pow_left₀ (show 0 ≤ (lawn (ships j)+(1:ℝ)) from by positivity) (show (lawn (ships j)+(1:ℝ)) ≤ (f:ℝ)*↑(stamp j) from (by exact_mod_cast supportM j)) _); rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast notch_one j.xy) (show r+3≤q by omega)) (by positivity)
         have hQ(i:ℕ)(hi:i≤r+2): HasSum (c i) (t^i *wholeX (timbre ships p i) (fun _=>v)):=by
              unfold c a; simp_rw [coinShots, _root_.mul_assoc]; exact (doReads h (by omega) (fun _=>v) (fun _=>hv)).mul_left _
         let d(j:Page (Shade G) k):=∑ i∈range (r+3),c i j; let g(j):= p j*a j t; let x:= K*t^(r+3)
         have ht:x≥0:=by unfold x; positivity
         have hp(j): ‖g j-d j‖≤ (figure q j*‖p j‖)*x:=by
              rw [show g j-d j= p j * (a j t-∑ i∈range (r+3), t^i * WardBin.leading i (a j)) by unfold d c g; rw [mul_sub,mul_sum]; congr 1; exact sum_congr rfl fun i hi=> by ring, norm_mul]; exact (mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)).trans_eq (by unfold x;ring)
         have hg:Summable (g-d):= (h.2.1.mul_right x).of_norm_bounded hp; have hs: HasSum d (∑ i∈range (r+3), t^i*wholeX (timbre ships p i) (fun _=>v)):= by
              apply hasSum_sum -- names
              intro i hi; exact hQ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
         have hj:Summable g:=sub_add_cancel g d ▸ (hg.add hs.summable); rw [← hs.tsum_eq]; change ‖(∑' i,g i)-_‖≤ _; rw [← hj.tsum_sub hs.summable]; apply (norm_tsum_le_tsum_norm (hg.norm)).trans; apply le_trans (hg.norm.tsum_le_tsum hp (h.2.1.mul_right x)); rw [tsum_mul_right, mul_assoc]; exact mul_le_mul_of_nonneg_right h.2.2 ht
end YM.OPE.Flume.Script
