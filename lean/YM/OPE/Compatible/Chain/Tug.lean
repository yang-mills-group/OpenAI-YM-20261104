import YM.OPE.Compatible.Chain.Catch
/-!
# same-ratio continuation on potentials also; Lipschitz-after-degradation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
lemma paysV (C:KernelChoices)(h:4≤r):∃ B:ℝ,0≤B ∧ ∀ v w:Train r, ∀ a≥0,∀ b≥0,(ShellRow C w-ShellRow C v).strip a b →∀ n:Side,∀ p:Site n,∀ i j:M,
   ‖(slender (ShellRow C v) p-slender (ShellRow C w) p) i j‖ ≤ B * Real.sqrt b*(win p)^(-(3:ℤ)):=by
      obtain ⟨c,hc,H⟩:= pole_pay h (C:=C) 
      let d:ℝ:= Fintype.card M; have hd:0≤d:=Nat.cast_nonneg _; let B:= Real.sqrt ((c+c)*(d*c*(d*c))); refine ⟨B,Real.sqrt_nonneg _,fun v w a ha b hb hx n p i j=>?_⟩
      let V:=ShellRow C v; let W:= ShellRow C w; let A:=spline V (mon p); let X:=spline W (mon p); let t:=win p; by_cases hp:p=0
      · unfold slender; subst p; simp only [↓reduceIte,sub_self,Matrix.zero_apply,norm_zero]; exact mul_nonneg (by unfold B; positivity) (zpow_nonneg (norm_nonneg _) _)
      have hu(o:Train r)(i j:M): ‖(spline (ShellRow C o) (mon p))⁻¹ i j‖ ≤ c/t^2:=by simpa only [under,bough,Complex.ofReal_zero,zero_smul,add_zero] using H o n p 0 le_rfl i j hp
      let m:=c/t^2; have hv(i j:M):‖X⁻¹ i j‖ ≤ m:=hu w i j; have hh(i j:M): ‖A⁻¹ i j‖ ≤ m:= hu v i j; unfold slender; rw [if_neg hp,if_neg hp]; let k:= ‖(A⁻¹-X⁻¹) i j‖
      have h1:k ≤ (c+c)/t^2:= (norm_sub_le ..).trans ((add_le_add (hh _ _) (hv _ _)).trans_eq (add_div ..).symm)
      have hm:t>0:= win_p _ hp
      have hX: A⁻¹-X⁻¹=A⁻¹*(X-A)*X⁻¹:= by have hA:IsUnit A.det:= conduit h v hp; have hW:IsUnit X.det:= conduit h w hp; rw [Matrix.mul_sub,Matrix.sub_mul,mul_assoc, Matrix.mul_nonsing_inv _ hW, mul_one,nonsing_inv_mul _ hA,Matrix.one_mul]
      have hr(i j:M): ‖(X-A) i j‖ ≤ b:=by
           have hp:Next.Free.physical (mon p):= real_frequency p
           have he:(X-A)=(W-V).read (mon p):=by rw [show ((W-V):Row M M)=(Work.F08.minusRows W V) from rfl,read_less (Op_whole h w|>.safe) (Op_whole h v|>.safe) hp]; unfold X A spline; abel
           rw [he]; exact row_entry_le hx ha (mon p) hp _ _ -- maybe too many
      have h2 : k ≤ d*c*(d*c)*b/t^4:=by unfold k; rw [hX]; apply (matrixPay _ _ (matrixPay _ _ hh hr) hv i j).trans; exact le_of_eq (by change d*(d*(m*b)*m)=_; unfold m;ring)
      have ht:c+c≥0:=add_nonneg hc.le hc.le; change k≤B* Real.sqrt b*t^(- (3:ℤ)); apply le_of_sq_le_sq (b:=B*_ * _) _ (by unfold B; positivity)
      rw [mul_pow, mul_pow B, Real.sq_sqrt hb,show B^2= _ from Real.sq_sqrt (show 0≤(c+c)*(d*c*(d*c)) by positivity)]
      refine le_trans ?_ (b:=(c+c)/t^2*(d*c*(d*c)*b/t^4)) (le_of_eq ?_); rw [pow_two]; apply mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      rw [_root_.zpow_neg]; field_simp
lemma told (C:KernelChoices)(h:4≤r):∃ B:ℝ, 0≤B ∧ ∀ v w:Train r,∀ a≥0,∀ b≥0,(ShellRow C w-ShellRow C v).strip a b→∀ n:Side,∀ i j,
    ‖(lineC (ShellRow C v) n-lineC (ShellRow C w) n) i j‖≤B*Real.sqrt b:=by
     obtain ⟨d,hd,H⟩:= paysV C h; obtain ⟨q,hq,ht⟩:= mantle_bill (k:=3) (by decide) le_rfl; refine ⟨d*q,by positivity,fun v w a ha b hb hx n i j=>?_⟩
     unfold lineC; rw [spectraMinus]; apply (spect_cost _ _ (fun p:Site n=>H v w a ha b hb hx n p i.2 j.2)).trans; rw [← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ht n) (show 0≤d*Real.sqrt b by positivity)) (show 0≤aquas n by unfold aquas; positivity)).trans; apply le_of_eq; unfold aquas; field_simp
end YM.OPE.Cascade.Terp
