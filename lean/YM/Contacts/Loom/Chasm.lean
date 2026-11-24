import YM.Contacts.Loom.Radar
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Patch
open Capture ConnectedActivityE6 Poll Push.AbsoluteSums Lantern MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
variable {D C Q:ℝ}  {d:ℕ→ℝ}
section barren
variable {ι:Type}[Fintype ι][DecidableEq ι]
lemma steamMoment (k:ℕ)(A:Matrix ι ι ℝ)(h:A.PosDef) (hp:∀ x:ι→ℝ,dotProduct x (A*ᵥx) ≤ C * dotProduct x x)(hz:(Fintype.card ι:ℝ)≤ D): let s:=D; let Φ(x: Body ι):=(buoy x)^k; Integrable Φ (sweep A) ∧ ∫ x,Φ x ∂sweep A ≤ (1+s)^k*(1+s*(2*Real.exp (C*k^2/2))) := by -- k^2 type cast check
   intro s Φ; have hf:0≤ s:= (Nat.cast_nonneg _).trans hz; let μ:=sweep A; have hk i:|A i i| ≤ C:= by
      let x:ι→ℝ:=Pi.single i 1; have he:A i i ≤ C:=by simpa only [x,mulVec_single_one, single_one_dotProduct,Matrix.col_apply,Pi.single_eq_same,mul_one] using! hp x
      have hb:0≤A i i:= (h.posSemidef.diag_nonneg); rwa [abs_of_nonneg hb]
   let F(x:Body ι):=∑ i,(1+|x i|)^k; obtain ⟨hM,H⟩:= Blaze.Flux.salience (ι:=ι) Finset.univ h.posSemidef hk k; rw [Finset.card_univ] at H
   let v t:= (1+s)^k*(1+F t); have hW (x : Body ι): Φ x≤ v x:= by
      cases isEmpty_or_nonempty ι with
      | inl h=> unfold v F Φ; simp only [Subsingleton.elim x 0,Fintype.sum_empty, buoy, norm_zero,add_zero,one_pow,mul_one]; exact one_le_pow₀ (by linarith)
      | inr h=> obtain ⟨z,hz',hT⟩:= Finset.exists_max_image Finset.univ (fun i=>|x i|) (Finset.univ_nonempty (α:=ι)); let a:=|x z|
                have hh : ‖x‖≤(1+s)*a:= by
                   rw [← sq_le_sq₀ (norm_nonneg _) (show 0≤(1+s)*a from (by unfold a; positivity)),EuclideanSpace.real_norm_sq_eq]; have ht:= Finset.sum_le_sum (g:=fun i=> a^2) (f:=fun i=> x i^2) (fun i hi=> (?_ : _≤ _)) (s:=univ); swap; · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hT i (mem_univ i)) 2
                   rw [sum_const,nsmul_eq_mul,card_univ] at ht; apply ht.trans; nlinarith only [pow_nonneg (a:=a) (by unfold a; positivity) 2,mul_le_mul_of_nonneg_right (show (Fintype.card ι:ℝ) ≤(1+s)^2 from by nlinarith only [hz,hf, sq_nonneg s]) (sq_nonneg a)] -- s definitional
                unfold Φ buoy; apply (pow_le_pow_left₀ (by positivity) (show 1+ ‖x‖≤(1+s)*(1+a) from by nlinarith) _).trans; unfold v; rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f:=fun i=>(1+|x i|)^k) (fun i _=>by positivity) (mem_univ z)).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
   have hi : Integrable v μ:= Integrable.const_mul ((integrable_const (1:ℝ)).add hM) _; have ht : Integrable Φ μ:= hi.mono' (by unfold Φ buoy; fun_prop) (Eventually.of_forall (fun z=> (Real.norm_of_nonneg (pow_nonneg (show 0≤ buoy z from by unfold buoy; positivity) k)).trans_le (hW z))); -- concret
   refine ⟨ht,(integral_mono ht hi hW).trans ?_⟩; unfold v; rw [integral_const_mul,integral_add (integrable_const _) hM,integral_const,probReal_univ, one_smul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply add_le_add_right; exact H.trans (mul_le_mul_of_nonneg_right hz (by positivity))
end barren
variable {I:ℕ→Type} [∀ i,Fintype (I i)][∀ i, DecidableEq (I i)]
variable (W:∀ i,Matrix (I i) (I i) ℝ)(h:∀ᶠ i in atTop,(W i).PosDef ∧ ∀ x,dotProduct x (W i *ᵥx) ≤ C*dotProduct x x)
include h
lemma distant (G:Gauge)(L:Side)(Y:ℝ→ℝ) (ht:Tendsto d atTop atTop)(hx:N.β =ᶠ[atTop] fun i=>betaF G (d i) L) (hf : ∀ᶠ i in atTop,(Fintype.card (I i):ℝ) ≤ Y (d i))(hr:Bolt G L Y)(hp:0<C)(hq:0<Q): Patch.Shell N (fun i=> sweep (W i)) (fun i=> Q*Delay.fineMonitor G L (d i)):= by
   let V i:= Body (I i); let X(i:ℕ):=coast (fun i=> Q*Delay.fineMonitor G L (d i)) V i; let μ i:=sweep (W i); let s i:= (μ i).restrict (X i)ᶜ
   have He k:= (h.and hf).mono (fun i hi=> steamMoment k _ hi.1.1 hi.1.2 hi.2); let F i:= Y (d i); have hF: N.Rush 0 F:= Rush.grounded hr.uses ht hx
   constructor; · exact fun k=> (He k).mono fun _ h=> h.1
   intro k p; let U (i:ℕ):= N.pow p i; have hu:= Rush.any (M:=N) (p:=p); let w (i:ℕ):= 1- (μ i).real (X i); have hX i:w i= (μ i).real ((X i)ᶜ):=(by rw [measureReal_compl measurableSet_closedBall,probReal_univ])
   have hw(q:ℝ): N.Rush q w:= by
      intro r _; filter_upwards [hx,h,hf,ht.eventually (walls G L hr hp hq r)] with i hx h hf ht; rw [Real.norm_of_nonneg (show 0≤w i from (by rw [hX]; positivity))]; unfold Meter.pow; rw [hx]; apply ht _ _ hf h.1 h.2
   let e i:= N.pow (-p) i; let R (k:ℕ)(t:ℝ):=(1+t)^k*(1+t*(2*Real.exp (C*k^2/2))); have hR n: N.Rush 0 (fun i=>R n (F i)):= by
      let h: N.Rush 0 (fun i=>1+F i):=(Rush.settle 1).blend hF; exact (h.powers n).times ((Rush.settle 1).blend (hF.bind _)) (by ring)
   let a:=k*2; have H':N.Rush p (fun i=> w i*e i+U i*R a (F i)):= ((hw (2*p)).times Rush.any (show 2*p + (-p) = p from by ring)).blend (hu.times (hR a) (add_zero _))
   apply H'.view; filter_upwards [N.eventual, He k, He a] with i hi ht hp; let f (k:ℕ)(z:V i):= buoy z ^k
   have hb:e i=(U i)⁻¹:=Real.rpow_neg hi.le p; have hh:0<U i:=Real.rpow_pos_of_pos hi _
   have hf k z:0≤f k z:=by unfold f buoy; positivity
   have hu : 0 ≤ ∫ y, f k y ∂(s i):= integral_nonneg (hf k); change ‖∫ z,f k z ∂(s i)‖ ≤ _; rw [Real.norm_of_nonneg hu]; apply le_trans _ (le_abs_self _)
   let F' x:= e i+ U i *f a x; have hF x: f k x ≤ F' x:= by
      have he x:f a x=f k x^2:=pow_mul ..; unfold F'; rw [he,hb]; apply le_of_mul_le_mul_left (a:=U i) _ hh; rw [mul_add,mul_inv_cancel₀ hh.ne']; nlinarith only [sq_nonneg (U i*f k x-1/2)]
   apply (integral_mono (μ:=s i) ht.1.integrableOn ((integrable_const _).add (hp.1.integrableOn.const_mul _)) hF).trans
   unfold s; simp only [Pi.add_apply]; rw [integral_add (integrable_const _) (hp.1.integrableOn.const_mul _),integral_const_mul,_root_.MeasureTheory.setIntegral_const]; change (μ i).real (X i)ᶜ * e i+ _ ≤ w i*e i+ _; rw [← hX]; exact add_le_add_right (mul_le_mul_of_nonneg_left ((setIntegral_le_integral hp.1 (Eventually.of_forall (hf a))).trans hp.2) hh.le) _
end Patch
end
end YM.Contacts.Loom
