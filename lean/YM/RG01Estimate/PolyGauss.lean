import YM.RG01Estimate.Fluctuate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogosG
/-!
# Cutting the finite jets with a uniform all-orders rate.

No inverse estimate in isolation (and no Euclidean-volume cutoff const). Number of closed
coordinates can be zero. The polynomial **norm** powers include sums over all coords.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.PolyGauss
open Function Filter Set Metric MeasureTheory Finset Matrix
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor Office
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {p c C E : ℝ} {k j m : ℕ} {Q : Matrix ι ι ℝ}
local notation "μ" => Poll.sweep Q
local notation "Y" => Poll.Body ι
local notation "D" => (Fintype.card ι:ℝ)
variable (hp:∀ z:ι→ℝ, dotProduct z (Q*ᵥ z)≤ c* dotProduct z z) (h : Q.PosDef)
-- k hidden, ensure included
include hp h
lemma diagonals (i:ι): |Q i i|≤ c:= by
   let z : ι→ℝ := Pi.single i 1
   have he := hp z; have hz : z≠0:= by
     intro h; have hh := congr_fun h i; simp [z] at hh
   have hq := h.dotProduct_mulVec_pos hz
   simp [z] at he hq
   rwa [abs_of_nonneg (show 0≤ Q i i from hq.le)]
-- norm estimate from max
local notation "X" => Finset.univ (α:=ι)
lemma total (j:ℕ) (F:ℝ) (hv:1≤F)(hF:D≤ F) :
    let f (x : Poll.Body ι):= (1+(‖x‖+1))^j
    Integrable f (μ) ∧ (∫ x,f x ∂μ) ≤ (2+F)^j * (1+F*(2*Real.exp (c*(j:ℝ)^2/2))) := by
    intro f
    let g i (x:Y):=(1+|x i|)^j; let w x:= (2+F)^j * (1+∑ i,g i x)
    obtain ⟨hm,hT⟩:= Blaze.Flux.salience (X) h.posSemidef (diagonals hp h) j
    have hi : Integrable w μ := ((integrable_const 1).add hm).const_mul _
    have hW x: f x ≤ w x:= by
      cases isEmpty_or_nonempty ι with
      | inl hv'=>
        have he:x=0:= Subsingleton.elim _ _
        rw [he]; unfold f w; rw [sum_of_isEmpty]; simp only [norm_zero,zero_add,add_zero,mul_one]; (gcongr; norm_num)
      | inr hv'=>
        obtain ⟨i,hk,hh⟩ := exists_max_image X (fun i=> |x i|) (Finset.univ_nonempty (α:=ι))
        have hL : ‖x‖ ≤ F* |x i| := by
          have hf : 0 ≤ F := zero_le_one.trans hv
          rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hf (abs_nonneg _)),EuclideanSpace.real_norm_sq_eq]
          apply le_trans (b:= ∑ _k:ι, |x i|^2)
          · exact Finset.sum_le_sum fun p h=> by rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hh _ h) _
          rw [sum_const,card_univ, nsmul_eq_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (hF.trans (le_self_pow₀ hv (by decide))) (sq_nonneg _)
        have ha : 1+(‖x‖+1) ≤ (2+F)*(1+|x i|):= by linarith [abs_nonneg (x i)]
        apply (pow_le_pow_left₀ (by positivity) ha j).trans
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (a:=i) (f:=fun j=> g j x) (fun _ _=> by unfold g; positivity) hk).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
    have hf : Integrable f μ := hi.mono' (by unfold f; fun_prop)
        (ae_of_all _ (fun x=> (Real.norm_of_nonneg (show 0≤ f x from by unfold f; positivity)).trans_le (hW x)))
    refine ⟨hf, (integral_mono hf hi hW).trans ?_⟩
    unfold w; rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [integral_add (integrable_const _) hm,integral_const,probReal_univ,one_smul]
    rw [card_univ] at hT
    exact add_le_add_right (hT.trans (mul_le_mul_of_nonneg_right hF (by positivity))) _

-- Cheap form of tail interpolation not Hölder. Square moment grows polynomial in sizes.
lemma weight_compl (F:ℝ) (hv:1≤F)(hF:D≤ F) (j : ℕ) (δ:ℝ) (hd:0<δ)
      (Z : Set (Poll.Body ι)) :
    ∫ i in Z, (1+(‖i‖+1))^j ∂μ ≤
       (μ).real Z * δ⁻¹ + δ*((2+F)^(j+j) * (1+F*(2*Real.exp (c*((j+j:ℕ):ℝ)^2/2)))) := by
    let f (i:ℕ) (x:Y):= (1+(‖x‖+1))^i
    obtain ⟨hI,H⟩:= total hp h (j+j) F hv hF; have hz:= (total hp h j F hv hF).1
    apply (le_trans ?_ (add_le_add le_rfl (mul_le_mul_of_nonneg_left H hd.le)))
    have he (x:Y): f j x ≤ δ⁻¹+ δ*f (j+j) x:= by
       have hG: δ⁻¹*δ=1:= inv_mul_cancel₀ hd.ne'
       change (1+_)^_ ≤ _ + δ * (1+_)^(_+_); rw [pow_add]
       let y:= f j x; change y ≤ δ⁻¹+δ*(y*y)
       apply le_of_mul_le_mul_left _ hd
       nlinarith only [hG,sq_nonneg (δ*y-1/2)]
    have ht : (∫ i in Z, f j i ∂μ)≤ ∫ i in Z,δ⁻¹+δ*f (j+j) i ∂μ:= setIntegral_mono
       hz.integrableOn ((integrable_const («μ»:=Poll.sweep Q) (δ⁻¹)).integrableOn.add ((hI.const_mul _).integrableOn)) he
    apply ht.trans
    rw [integral_add (integrable_const _) ((hI.const_mul _).integrableOn), setIntegral_const,integral_const_mul]
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hI (ae_of_all _ (fun b=> by positivity))) hd.le
section stages
omit hp h
open YM.Lattice YM.Pressure Push.AbsoluteSums Sienna
variable {G : Gauge} {L : Side} {F : ℝ→ℝ}
def costs (j:ℕ)(t p: ℝ):= (2+t)^j*(1+t*(2*Real.exp (p*(j:ℝ)^2/2)))
lemma costs_poly (j:ℕ) (F:ℝ→ℝ)(he:Bolt G L F)(p:ℝ) : Bolt G L (fun x=> costs j (F x) p):= by
   exact (((Bolt.still 2).joins he).nod j).times ((Bolt.still 1).joins (he.times (Bolt.still _)))

lemma walls (j:ℕ)(c d m:ℝ)(hc:0<c)(hd:0<d)(he:Bolt G L F):
       ∀ᶠ t in atTop, ∀ (ι:Type)[Fintype ι][DecidableEq ι](W : Matrix ι ι ℝ), (Fintype.card ι:ℝ)≤ F t → 1 ≤ F t → W.PosDef →
       (∀ i:ι→ℝ, dotProduct i (W *ᵥ i) ≤ c * dotProduct i i) →
           (∫ i in (closedBall (0:Poll.Body ι) (wick G L d t))ᶜ, (1+(‖i‖+1))^j ∂(Poll.sweep W)) ≤ (betaF G t L)^m:= by
   let u := m-1
   let a:= m -1 + u
   have hh := Lantern.walls G L he hc hd a; have hg:= Rate.power (G:=G) (L:=L) (a:=u)
   have hp : Rate G L u (fun x=> betaF G x L^a*(betaF G x L ^ u)⁻¹) := by
      refine hg.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx
      rw [← Real.rpow_neg hx.le,← Real.rpow_add hx, show a+ -u=u by unfold a u; ring]
   have hF:= costs_poly (j+j) F he c
   have hr := (hp.add ((hg.mul hF.uses).weaken (le_of_eq (add_zero ..)))) m (by unfold u; linarith)
   filter_upwards [hh, hr, Delay.shift_pos G L] with t hH ht hx ι _ _ W hQ hS h hσ
   let Z:= closedBall (0:Poll.Body ι) (wick G L d t); let B:= Poll.sweep W; let b:= betaF G t L
   have ht' := hH _ W hQ h hσ
   have hf : B.real Zᶜ ≤ b^a:= by rw [measureReal_compl measurableSet_closedBall, probReal_univ]; exact ht'
   have hd : 0 < b^u:= Real.rpow_pos_of_pos hx _
   exact (weight_compl hσ h _ hS hQ j (b^u) hd Zᶜ).trans ((add_le_add_left (mul_le_mul_of_nonneg_right hf (inv_pos.mpr hd).le) _).trans ((le_abs_self _).trans ht))
end stages
end YM.RG01Estimate.PolyGauss
