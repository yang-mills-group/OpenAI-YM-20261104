import YM.AveragedStep.Orders.Insignia
/-! Assembly of physical estimates for the polynomialized equation. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f k d:ℕ} {G: Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}
variable {Q:Cuff P K A} {B D δ:ℝ}(H:Cadence Q B D δ)
include H
lemma labor (hA:LocalRatio A)(h:P.Branches K G) (i:G.ColorIndex)(k d:ℕ):
    let n:=2*k+2*d+6
    ∃ X:ℝ,0≤X∧∀{c f:Side}(S:StepData c f)(F:Forest S.ratio)(hP:S.patch=P)(hK:S.kernel=K)(w:List (Ink G c f)),w.length=k →∀ (x:Site c)(j:F.Free){τ:ℝ},1≤τ→∀ z:TopologyQ F G,
      let q:Cuff S.patch S.kernel A:=hP.symm ▸ hK.symm ▸ Q
      let U:=cup F x τ (aisle (S:=S) (Sum.inl j.val) w) z
      |tub F q x j i w d τ z| ≤ X*U^n ∧ |arbor F q x j i w d τ z| ≤ X*τ⁻¹^(d+1)* U^n:=by
 intro n
 let v:=fingers G i
 obtain ⟨E,hE,T⟩:=chorus_cost P K A v d
 obtain ⟨M,hM,L⟩:=chorus_shops Q hA h v d
 let Z:=B^k; let y:ℝ:=2*((k:ℝ)*Z+Z*(E*B^(d+1)))+D*Z
 let m:=Z*M*(B^(d+2)); have hB:= H.price; have hD:= H.second
 have hZ:0≤Z:=by unfold Z; positivity
 refine ⟨max y m,by unfold y m; positivity,?_⟩; intro c f S F hP hK w hw x j τ ht z
 subst P K; dsimp only
 let e:Rim c f:=Sum.inl j.val
 let U:=cup F x τ (aisle (S:=S) e w) z
 let g:=hands F Q x τ z
 have He(z: Rim c f)(h:z∈aisle (S:=S) e w):‖g z‖≤ B*U:=hands_cost F Q H.log hB τ ht x _ _ z h
 have hU:1≤U:=cup_ge F x τ (zero_le_one.trans ht) ..
 have hr:1≤ B*U :=one_le_mul_of_one_le_of_one_le hB hU
 have hIn(p)(hh:p∈w):‖g p.1‖≤ B*U:=He _ (aisle_slot hh) -- arguments
 obtain ⟨h₁,h₂⟩:=peel_pay (fieldKey F j i) w g hr hIn; rw [hw,mul_pow] at h₁ h₂
 let A₀:= chorus S A τ⁻¹ e v d g
 have h3: |A₀|≤E*(B^(d+1)*U^(d+1)):=by rw [←mul_pow]; exact T S rfl rfl _ _ hr (by positivity) ((inv_le_one₀ (by positivity)).mpr ht) (fun l hl=> He _ (aisle_home e w hl))
 let G₀:=mon w g
 let K₀:=peel (fieldKey F j i) w g
 let W₀:=live F Q x j z
 let Q₀:=Q.incline v (F.drape z.1 j.val)
 let R:= outerGate F Q x j z
 obtain ⟨hf,hR⟩:=live_range F Q x j z
 have hb3:|τ⁻¹*R*Q₀*G₀|≤ (D*Z)*U^k:= calc
   _ = |τ⁻¹| * |R| * |Q₀| * |G₀|:=by simp only [abs_mul]
   _ ≤ 1*1*D*(Z*U^k):= by
     have he: |Q₀| ≤ D:=H.rate ..
     gcongr
     · rw [abs_of_pos (by positivity:(0:ℝ)<τ⁻¹)]; exact (inv_le_one₀ (by positivity)).mpr ht
   _ = _:=by ring
 constructor
 · unfold tub; change |(W₀-1)*(K₀-G₀*A₀)+_|≤ _ * U^n
   apply (abs_add_le ..).trans
   rw [abs_mul]; have hh:|W₀-1|≤2:= (abs_sub ..).trans (by rw [abs_one]; linarith)
   have hX:|K₀-G₀*A₀|≤(k:ℝ)*(Z*U^k)+(Z*U^k)*(E*(B^(d+1)*U^(d+1))):= (abs_sub ..).trans (by rw [abs_mul]; gcongr)
   let Y:ℝ:=(k:ℝ)*Z+Z*(E*B^(d+1))
   have hd₁ : U^k ≤ U^n:=pow_le_pow_right₀ hU (by unfold n; omega)
   have hd₂ : U^k*U^(d+1) ≤ U^n:= by rw [←pow_add]; gcongr; unfold n; omega
   have hV : |K₀-G₀*A₀|≤ Y*U^n:= by
     apply hX.trans
     rw [show (k:ℝ)*(Z*U^k)+(Z*U^k)*(E*(B^(d+1)*U^(d+1)))=(k:ℝ)*Z*U^k+(Z*(E*B^(d+1)))*(U^k*U^(d+1)) by ring]
     unfold Y; rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hd₁ (by positivity)) (mul_le_mul_of_nonneg_left hd₂ (by positivity))
   calc
     _ ≤ 2*(Y*U^n)+(D*Z)*U^n:= add_le_add (mul_le_mul hh hV (abs_nonneg _) (by norm_num)) (hb3.trans (mul_le_mul_of_nonneg_left hd₁ (by positivity)))
     _ ≤ _:= by rw [show 2*(Y*U^n)+(D*Z)*U^n=y*U^n from by unfold Y y; ring]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
-- next arbor
 have h0τ:0<τ:=zero_lt_one.trans_le ht
 have hz:τ⁻¹ • g=grasp F Q x z:=by unfold g hands; rw [smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
 let u:=aboard F x z e
 have ht0:τ⁻¹ • (g e)=Q.logC u:=congr_fun hz e
 have he:= L S rfl rfl e g hr (inv_pos.mpr h0τ) (fun l hl=> ⟨He l (aisle_home e w hl), by
    rw [show τ⁻¹ • g l=Q.logC _ from congr_fun hz l]; exact Q.log_max _⟩)
 dsimp only at he; rw [hz,ht0,inv_inv] at he
 let f0:=flame Q e (grasp F Q x z) v
 let D0:=Cuff.haarScore (A:=A) (Q.logC u) v
 change |(τ*f0-τ⁻¹*D0)-A₀|≤ _ at he
 have hb : arbor F Q x j i w d τ z = W₀*G₀*(-((τ*f0-τ⁻¹*D0)-A₀)):=by
    unfold arbor sdEq tub; dsimp only; rw [map_smul]; simp only [smul_eq_mul];
    change τ⁻¹*(R*Q₀*G₀+W₀*(τ*(fderiv ℝ (mon w) g (introAt e v))+G₀*(D0-τ^2*f0)))-(K₀-G₀*A₀)-((W₀-1)*(K₀-G₀*A₀)+τ⁻¹*R*Q₀*G₀)=_
    rw [show fderiv ℝ (mon w) g (introAt e v)=K₀ from peels (fieldKey F j i) w g]
    field_simp; ring
 rw [hb,abs_mul,abs_mul,abs_neg]; change _≤_ * U^n
 have hk : U^k*U^(d+2) ≤ U^n:=by rw [←pow_add]; gcongr; unfold n; omega
 let J:=τ⁻¹^(d+1)
 have hJ:0≤J:=by unfold J; positivity
 calc
    _ ≤ 1*(Z*U^k)*(M*J*(B*U)^(d+2)):=by gcongr
    _ = (Z*M*B^(d+2))*J*(U^k*U^(d+2)):=by rw [mul_pow]; ring
    _ ≤ _:=by gcongr; exact le_max_right ..
end YM.AveragedStep
