import YM.Juniper.Mulberry.Altitude
/-!
 # Quantitative upload of k-jet Regular Earnings

 Actual *cut+Body* to ℝ^m probability, remember radius scales. Coefficient
 costs w.r.t. canonical tensors. Includes no positivity assumption on hard
 sheets. Charges dimensions before sizing SECOND stamps (unrelated Beta
 phases not part of this ledger).
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        {b s a q v w t:ℝ}{k n j:ℕ}
section probability
variable {ι : Type}[Fintype ι][DecidableEq ι]
    (Y: Matrix ι ι ℝ) (D: ℝ) {f:Poll.Body ι → E→ℝ}{x:E}
local notation "r"=> (1+ j)
local notation "μ"=> sweep Y
local notation "Ψ"=> closedBall (0:Poll.Body ι) D
local notation "Φ"=> full μ f
local notation "F"=> cut μ Ψ f
local notation "g"=> fun i: ℕ=>Tensor.coeff F i 0
variable (hk:0<b)(p: Paint (closedBall (0:Poll.Body ι) D) k f b q)(h : ∀ y∈Icc (-1:ℝ) 1, Brush k w 1 Real.exp y)
    (hg: ∀ i≤ k, AEStronglyMeasurable (fun z=> Tensor.coeff (Real.exp ∘ f z) i 0) (sweep Y))
variable (hb: ∀ z:Poll.Body ι, Brush k (a * LocalAtlas.bill j z) 1 (f z) 0)
    {c θ:ℝ} (hr : Y.PosDef) (hc:∀ z:ι→ℝ, dotProduct z (Y*ᵥ z) ≤ c*dotProduct z z)(hA:(Fintype.card ι:ℝ)≤ θ)
include p hb
omit [FiniteDimensional ℝ E] [DecidableEq ι] p in
lemma nonneg_a : 0≤a:= by simpa [LocalAtlas.bill] using (hb 0).nonneg
include h
local notation "o"=> j*k
local notation "p!"=> clump k a w
local notation "P"=> fun i:ℕ=> fun z:Poll.Body ι=> Tensor.coeff (Real.exp ∘ f z) i 0
omit [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma open_at (z:Poll.Body ι) : Brush k (p! * LocalAtlas.bill (j*k) z) 1 (Real.exp ∘ f z) 0:=by
   let V:= LocalAtlas.bill j z; have hV:1 ≤ V:= one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z)); have ha:=nonneg_a hb
   have h₁:= (h 0 (by simp)).nonneg; have hh:= p.air z
   refine (Lantern.composite (hb z) (show Brush k w 1 Real.exp (f z 0) from hh ▸ h 0 (by simp))).climb ?_ le_rfl
   unfold clump; rw [mul_assoc (k.factorial*w),show bill (j*k) z = V^k from pow_mul ..,← mul_pow]; gcongr; dsimp only [V] at *; nlinarith only [hV]
include hg hA hc hr hk
local notation "P₀"=> (p! * gamut θ c (j*k))
local notation "e"=> p! * (s*gamut θ c (2*(j*k))+ v*s⁻¹)
omit hk in
omit [FiniteDimensional ℝ E] in
lemma earnings {i:ℕ}(hi:i ≤ k) : Integrable (P i) μ ∧ ‖Φ i‖ ≤ P₀:= by
   let ξ:= moment hr hc hA (j*k); have hx(z:Poll.Body ι) : ‖P i z‖ ≤ p!*LocalAtlas.bill (j*k) z := LocalAtlas.capped (open_at D p h hb z) i hi
   have hf:= (ξ.1.const_mul (p!)); have hv:= (ae_of_all μ hx); have hp:=hf.mono' (hg i hi) hv; refine ⟨hp,(norm_integral_le_of_norm_le hf hv).trans ?_⟩
   rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ξ.2 (show 0 ≤ p! from by have hW:= nonneg_a hb; have hi:=(h 0 (by simp)).nonneg; unfold clump; positivity)
variable (he:(sweep Y).real (closedBall (0:Poll.Body ι) D)ᶜ ≤ v)
include he
lemma at_nose (hn:n+1 ≤ k)(hs:0<s) : cap (g - Φ) n e:= by
    intro i hi; have hi':i ≤ k:= by omega
    let P':= (P i); have hU:= earnings Y D p h hg hb hr hc hA hi' -- args include hk lint
    rw [Pi.sub_apply]; rw [origin p measurableSet_closedBall (by omega) h hk i hi', full, ← integral_add_compl measurableSet_closedBall hU.1]; rw [norm_sub_rev,add_sub_cancel_left]
    have hP: 0 ≤ p!:= by unfold clump; have he:= (h 0 (by simp)).nonneg; have hx:= nonneg_a hb; positivity
    refine (norm_integral_le_of_norm_le («g»:=fun z=> p!* LocalAtlas.bill o z) (((moment hr hc hA (j*k)).1.const_mul _).integrableOn) (Eventually.of_forall fun z=> LocalAtlas.capped (open_at D p h hb z) i hi')).trans ?_
    rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (LocalAtlas.outside hr hc hA o (Ψᶜ) measurableSet_closedBall.compl he hs) hP -- macro Ψ^c
end probability
end YM.Juniper.Mulberry
