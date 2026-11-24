import YM.RG01Estimate.SeriesCompose
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Series
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k m l r : ℕ}{b u v t:ℝ}{z:X}{f:X→ℝ}{P:Policy X ℝ}

def trimLead (P:Policy X ℝ) : Policy X ℝ:= fun i x=> P i x+ if i=0 then (-1:ℝ) else 0
omit [NormedSpace ℝ X] in
lemma trim_zero (hx : P 0 =ᶠ[𝓝 z] 1): trimLead P 0=ᶠ[𝓝 z] 0:= hx.mono fun i hi=>by unfold trimLead; simp only [hi,if_true,Pi.one_apply,Pi.zero_apply]; ring
lemma trimmed (p:Hon b r n P f t z)(hr:0<r): Hon b r n (trimLead P) (fun x=> f x + -1) (t+1) z:= by
   have hx := p.more (Hon.constant (-1) hr); rw [norm_neg,norm_one] at hx; exact hx

def logUnit (x:ℝ):= Real.log (1+x)
def invUnit (x:ℝ):= (1+x)⁻¹

def logarithm (P : Policy X ℝ) (n:ℕ):Policy X ℝ := Series.lift logUnit n (trimLead P)
def inverse (P:Policy X ℝ)(n:ℕ):Policy X ℝ := Series.lift invUnit n (trimLead P)

lemma smalls (D:ℕ):∃ v w:ℝ, (∀ x∈ball (0:ℝ) (1/2), Brush D v 1 logUnit x) ∧ (∀ x∈ball (0:ℝ) (1/2), Brush D w 1 invUnit x) := by
   let S:= closedBall (0:ℝ) (1/2); have h' (x:ℝ) (hx:x∈ S) : (1+x)≠ 0 := Ne.symm ((by linarith only [show -(1/2:ℝ)≤x from (abs_le.mp (mem_closedBall_zero_iff.mp hx)).1]: 0 < 1+x).ne)
   obtain ⟨v,hv,H⟩:= Brush.compact (k:=D) (isCompact_closedBall ..) (fun x (hx:x∈ S)=> (show ContDiffAt ℝ (D:WithTop ℕ∞) logUnit x from (Real.contDiffAt_log.mpr (h' x hx)) |>.comp (f:=fun x:ℝ=>1+x) x (contDiffAt_const.add contDiffAt_id))) -- edit
   have h : ∀ x∈S,ContDiffAt ℝ (D:WithTop ℕ∞) invUnit x:= fun x hx=> (contDiffAt_const.add contDiffAt_id).inv (h' x hx)
   obtain ⟨w,hw,J⟩:= Brush.compact (isCompact_closedBall ..) h
   exact ⟨v,w,fun x hx=> H x (ball_subset_closedBall hx),fun x hx=> J x (ball_subset_closedBall hx)⟩

lemma reciprocal (hr:0<r)(hp:Hon b r n P f t z)(hx:P 0=ᶠ[𝓝 z] 1)(hb:|b|≤1)
    (h:r*(t+1)*|b|+(t+1)*|b| < 1/2)(he:∀ x∈ball 0 (1/2), Brush (n+r) v 1 logUnit x)(hh:∀ x∈ball 0 (1/2), Brush (n+r) u 1 invUnit x):
     1/2 < f z ∧
     Hon b r n (logarithm P r) (Real.log ∘ f) (desk logUnit r n (t+1) v) z ∧
     Hon b r n (Series.inverse P r) (fun x=> (f x)⁻¹) (desk invUnit r n (t+1) u) z:= by
   rw [← add_mul] at h; have hp' := trimmed hp hr; have ht:=trim_zero hx; have hw := hp'.closed hr hb ht
   have hz : 1/2 < f z:= by linarith only [(abs_lt.mp (show |f z + -1| < 1/2 from hw.bound.trans_lt h)).1]
   refine ⟨hz, (Hon.compose logUnit hp' ht he hr hb h).shift (Eventually.of_forall fun x=> ?_) (fun _ _=> EventuallyEq.rfl), (Hon.compose invUnit hp' ht hh hr hb h).shift (Eventually.of_forall fun x=>?_) (fun _ _=> EventuallyEq.rfl)⟩
   · change Real.log (f x)=Real.log (1+(_+_)); ring_nf
   change (f x)⁻¹=(1+(_+_):ℝ)⁻¹; ring_nf

open Laplace Lattice Coat Pressure Sienna
lemma normalizes (G:Gauge)(L:Side)(r n:ℕ)(f:ℝ→ℝ)(hr:0<r)(hp:Cookie G L f) :
   ∃ C D:ℝ→ℝ, Cookie G L C ∧ Cookie G L D ∧ ∀ᶠ t in atTop,
       ∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X]
         (A:X→ℝ)(P:Policy X ℝ)(z:X) (β:ℝ), betaF G t L/2 ≤ β →
         let b:= gStep β
         Hon b r n P A (f t) z → (P 0 =ᶠ[𝓝 z] 1) →
       1/2 < A z ∧ b ≤ 1∧0<b ∧ Hon b r n (Series.logarithm P r) (Real.log ∘ A) (C t) z ∧ Hon b r n (inverse P r) (fun x=> (A x)⁻¹) (D t) z := by
   obtain ⟨V,W,v,w⟩:= smalls (n+r)
   have hs:= glim G L; let hf:= hp.joins (Cookie.const 1); have hρ:= hf.uses.mul hs; have hθ:= ((hρ.mul_left (r:ℝ)).add hρ).below (by norm_num) (1/4) (by norm_num)
   refine ⟨_,_,pay_desk logUnit n r hf V,pay_desk invUnit n r hf W,?_⟩
   filter_upwards [hθ, hs.below (by norm_num) 1 zero_lt_one,Push.AbsoluteSums.Delay.shift_pos G L] with t hh hg ht X _ _ A P z β hβ b H HX
   obtain ⟨hy,hB⟩:=lamp G L ht β hβ
   have hplus : 0 < f t+1:= add_pos_of_nonneg_of_pos H.positive zero_lt_one
   have he:b≤ 1:= hB.trans ((le_abs_self _).trans hg)
   obtain ⟨hz,hv⟩:= reciprocal hr H HX (by simpa only [abs_of_pos (show 0<b from hy)] using he) (show r*(f t+1)*|b|+(f t+1)*|b|<1/2 by
     have hK := (le_abs_self _).trans hh; rw [abs_of_pos (show 0<b from hy), mul_assoc]; exact (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hplus.le) (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left hB (by linarith only [hplus]))).trans_lt (hK.trans_lt (by norm_num))) v w
   exact ⟨hz,he,hy,hv⟩ -- hplus edit

lemma Hon.canonically (A : X→E)(N:Policy X E){g:X→ ℝ}(hy:|b|≤1)(f:Hon b r n (Series.inverse P r) (fun x=> (g x:ℝ)⁻¹) u z)(h : Hon b r n N A v z) : Hon b r n (convolve (ContinuousLinearMap.lsmul ℝ ℝ) (Series.inverse P r) N) (fun x=> (g x)⁻¹ • A x) (addition n r 1 u v) z:=
 f.twins h (ContinuousLinearMap.lsmul ℝ ℝ) (by assumption) (ContinuousLinearMap.opNorm_lsmul_le ..)
end YM.RG01Estimate.Series
