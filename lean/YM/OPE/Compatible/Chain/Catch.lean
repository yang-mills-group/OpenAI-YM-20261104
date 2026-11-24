import YM.OPE.Compatible.Chain.Wheel
/-!
# uniform spatial sup cost & Hölder control with weights. -/
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
abbrev aquas (s:Side):ℝ:= ((s.val:ℝ)^4)⁻¹
lemma spect_cost {X:Site n→Matrix M M ℂ}(p q:Body 1 n){f:Site n→ℝ}(h:∀ x, ‖X x p.2 q.2‖ ≤ f x): ‖realOf (spectral X) p q‖ ≤ aquas n * (∑ x, f x):=by
      rcases p with ⟨p,i⟩; rcases q with ⟨q,j⟩; unfold realOf; rw [Matrix.map_apply,Real.norm_eq_abs]; apply (Complex.abs_re_le_norm _).trans; rw [spectral_apply,norm_mul]; rw [show ‖meter n‖=aquas n from ?_]; swap
      · have ht: meter n= Complex.ofReal (aquas n) := by simp [Further.FreeCovariance.KP.meter,aquas]
        rw [ht,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold aquas; positivity)]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun x _=>?_)) (by unfold aquas; positivity); rw [norm_mul,show ‖cell x (p-q)‖= (1:ℝ) from mode_real _ _ (real_frequency _),one_mul]; exact h _
lemma spectraMinus {X Y:Site n→Matrix M M ℂ} : realOf (spectral X)-realOf (spectral Y)=realOf (spectral (fun p=> X p-Y p)):=by
      have he:spectral (fun p=> X p-Y p)+spectral Y=spectral X:=by rw [spectral_add]; simp
      rw [show spectral (fun p=> X p-Y p)=_ from eq_sub_of_add_eq he]; ext i j; simp [realOf]
lemma terra_money (C:KernelChoices)(h:4 ≤ r):∃ B:ℝ,0≤B∧∀ v:Train r,∀ n:Side,∀ i j,‖lineC (ShellRow C v) n i j‖≤B:=by
      obtain ⟨b,hb,H⟩:= pole_pay (C:=C) h
      obtain ⟨d,hd,hh⟩:= mantle_bill (k:=2) (by norm_num) (by norm_num)
      refine ⟨b*d,mul_nonneg hb.le hd,fun v n i j=>?_⟩; let f(p:Site n):ℝ:=(win p)^(- ((2:ℕ):ℤ)); unfold lineC
      apply (spect_cost (X:=slender (ShellRow C v)) i j (f:=fun i=> b*f i) ?_).trans
      · rw [← Finset.mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh n) hb.le) (show 0≤aquas n from by unfold aquas; positivity)); refine le_of_eq ?_; unfold aquas; field_simp
      intro p; by_cases ht:p=0; · unfold slender; rw [if_pos ht]; change ‖(0:ℂ)‖≤_; rw [norm_zero]; exact mul_nonneg hb.le (zpow_nonneg (norm_nonneg _) _)
      unfold slender; rw [if_neg ht]; simpa only [under,bough,Complex.ofReal_zero,zero_smul,add_zero,f,_root_.zpow_neg,zpow_natCast,div_eq_mul_inv] using! H v n p 0 le_rfl i.2 j.2 ht
lemma tree_cost (C:KernelChoices) (h:4≤r):∃ d:ℝ, 0 ≤ d ∧ ∀ v:Train r,∀ u>0,∀ n:Side,∀ i j, ‖(major (ShellRow C v) n+u • 1)⁻¹ i j-lineC (ShellRow C v) n i j‖ ≤ d*Real.sqrt u+aquas n*u⁻¹:=by
      obtain ⟨b,hb,H⟩:= pole_changed h (C:=C); obtain ⟨d,hd,hD⟩:= mantle_bill (k:=3) (by norm_num) le_rfl; refine ⟨d*b,by positivity,fun v u hu n i j=>?_⟩
      rw [← pole_mass v h hu n]; unfold lineC; let X:= ShellRow C v; rw [← Matrix.sub_apply,spectraMinus]; apply (spect_cost _ _ (fun p:Site n=> H v n p u hu i.2 j.2)).trans
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,sum_ite_eq',mem_univ,if_true,mul_add]; gcongr ?_ + _; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD n) (show 0≤ b*Real.sqrt u from by positivity)) (show 0≤aquas n from by unfold aquas;positivity)); apply le_of_eq; unfold aquas; field_simp
end YM.OPE.Cascade.Terp
