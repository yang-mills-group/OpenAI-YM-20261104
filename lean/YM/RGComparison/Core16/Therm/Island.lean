import YM.RGComparison.Core16.Therm.Scroll
import YM.PertExtension.PTBills
/-!
# Proof of equivalence of linear-center and stationary-center Gaussian series

Both use full stationary Gaussian. This removes any ambiguity as to whether the nonlinear
station might induce wrong kinetic jets, before we compute those jets by a second (thermal)
equation. Work after fixing torus and F (internal tree), compare coefficients themselves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Therm
open Function Filter MeasureTheory Set Metric Asymptotics
open scoped Topology ContDiff NNReal
open PertExtension PertExtension.Series Tested Radial
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {K K' f f' : ℝ × E→ℝ} (u : ℝ → E) (v : ℝ)
    (h₁ : lit K f) (h₂ : lit K' f')

-- replacing `b = station + z` by `b = ...`; first coordinate shift parameter ℝ external.
def tilt (u : ℝ→E) (w : ℝ×E) := (w.1,u w.1+w.2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tilt_comp : tilt (-u) ∘ tilt u = id := by ext w <;> simp [tilt]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma passes {u : ℝ→E}{K f : ℝ × E→ℝ}(h : K = f ∘ tilt u) : f= K ∘ tilt (-u) := by rw [h,Function.comp_assoc,show tilt u ∘ tilt (-u)=id from by simpa only [neg_neg] using tilt_comp (-u),comp_id]

lemma on_axis {t y r : ℝ} (ht : 0 < t)
    (he : ‖u (t*v)‖ < r-y) (ha : IntegrableOn (fun x:E=> projection K f t (v,x)) (disc t r) μ) (hb : 0 ≤ᵐ[μ.restrict (disc t r)] (fun x:E=>projection K f t (v,x))) :
    chartLine μ (K ∘ tilt u) (f ∘ tilt u) v t y ≤ chartLine μ K f v t r := by
  let p := t⁻¹ • u (t*v); let X:= MeasurableEquiv.addLeft p; let S := disc (E:=E) t y; let T:=disc (E:=E) t r
  let F := fun i:E=> projection K f t (v,i)
  have ht' (x:E) : tilt u (t • (v,x)) = t • (v,X x) := by
    ext1
    · rfl
    change u (t*v)+t • x=t • (t⁻¹ • u (t*v)+x); rw [smul_add,smul_inv_smul₀ ht.ne']
  have hi (x : E) : projection (K ∘ tilt u) (f ∘ tilt u) t (v,x)= F (X x) := by
    unfold F; rw [projection_eq,projection_eq]; simp only [Function.comp_apply,ht']
  have hst : X ⁻¹' (X '' S) = S:= preimage_image_eq _ X.injective
  have hhX : MeasurePreserving X μ μ := measurePreserving_add_left μ p
  unfold chartLine; simp_rw [hi]; change (∫ x in S,F (X x) ∂μ) ≤ ∫ x in T,F x ∂μ
  rw [←hst, hhX.setIntegral_preimage_emb X.measurableEmbedding]
  refine setIntegral_mono_set ha hb (Filter.Eventually.of_forall fun i (h : i ∈ X '' S)=> ?_)
  obtain ⟨i,hi,rfl⟩:= h
  have hh : t*‖p‖=‖u (t*v)‖:= by simp only [p,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  exact (disc_mem ht.le r _).mpr ((mul_le_mul_of_nonneg_left (norm_add_le p i) ht.le).trans_lt (by linarith [(disc_mem ht.le y i).mp hi]))

include h₁ in
lemma greater (he : Tendsto u (𝓝 0) (𝓝 0)) : ∃ δ > 0, ∀ r ∈ Ioo 0 δ, ∀ y∈Ioo 0 r,
    ∀ᶠ t in Tested.germ, chartLine μ (K ∘ tilt u) (f ∘ tilt u) v t y ≤ chartLine μ K f v t r:= by
  obtain ⟨δ,hδ,hd⟩:= h₁.ranges μ v
  refine ⟨δ,hδ,fun r hr y hy=>?_⟩; have hu : Tendsto (fun t : ℝ=>u (t*v)) Tested.germ (𝓝 0):= he.comp (Tendsto.mono_left (by simpa [id_eq,zero_mul] using (continuous_id.mul_const v).tendsto 0) nhdsWithin_le_nhds)
  filter_upwards [eventually_pos, hu.eventually (ball_mem_nhds 0 (sub_pos.mpr hy.2)), hd r hr] with t ht hv hz
  exact on_axis μ u v ht (mem_ball_zero_iff.mp hv) hz.1 hz.2

omit μ in
lemma concord (u v : ℕ→ℝ) (k : ℕ) (ht : Bill (k+1) (peval u k - peval v k)) : ∀ i ≤ k, u i=v i := by
  have he : Bill (k+1) (peval (u-v) k) := by
    convert ht using 1; funext t
    unfold peval Zone.eval; simp only [Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
  intro i hi; have hh:= (Aspiration.polynomial (u-v) k).vanish he (Nat.lt_succ_of_le hi); exact sub_eq_zero.mp (by simpa [hi] using hh)

omit μ in
lemma hear (u v : ℕ→ℝ) (k : ℕ) (g f : ℝ→ℝ)
    (hF : Bill (k+1) (g - peval u k)) (hG : Bill (k+1) (f - peval v k)) (h : g ≤ᶠ[Tested.germ] f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in Tested.germ, peval u k x≤ peval v k x + C*x^(k+1):= by
  obtain ⟨C,hC,hF⟩:= hF; obtain ⟨D,hD,hG⟩:= hG; refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,hF,hG] with x hx hy hz; rw [Real.norm_eq_abs,Pi.sub_apply,abs_le] at hy hz
  obtain ⟨hy,-⟩:=hy; obtain ⟨-,hz⟩:=hz; linarith

structure Secured (f K : ℝ × E → ℝ) : Prop where
  spread : Stationary f
  slope : ∃ c>0, ∀ u : ℝ×E,c*‖u‖^2≤ jet f 2 u
  paid : lit K f

variable (hF : Secured f K) (hG : Secured f' K')

include hF hG in
lemma tilt_stamp_le (k : ℕ) (hk : K' = K ∘ tilt u) (hf : f' = f ∘ tilt u) (he : Tendsto u (𝓝 0) (𝓝 0)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in Tested.germ,
    peval (stamp μ K' f' v) k x ≤ peval (stamp μ K f v) k x + C*x^(k+1):= by
  obtain ⟨r,hp,hr⟩:= greater μ u v hF.paid he; rw [← hk, ← hf] at hr
  obtain ⟨d,hd,hD⟩:= aspirates μ _ _ k v hF.spread hF.paid.2.1 hF.paid.1 hF.slope
  obtain ⟨e,hE,h⟩:= aspirates μ _ _ k v hG.spread hG.paid.2.1 hG.paid.1 hG.slope
  obtain ⟨r',hb,hz⟩:= exists_between (lt_min hp hd); obtain ⟨hr',hrd⟩:= lt_min_iff.mp hz
  obtain ⟨y,ha,hz⟩:= exists_between (lt_min hb hE); obtain ⟨hx,hy⟩:= lt_min_iff.mp hz
  exact hear _ _ k _ _ (h _ ⟨ha,hy⟩) (hD _ ⟨hb,hrd⟩) (hr _ ⟨hb,hr'⟩ _ ⟨ha,hx⟩)

/-- ALL stamps agree. Coarse quadratic artificial pad is unchanged on both. θ subsequently. -/
theorem tilt_certified (he : Tendsto u (𝓝 0) (𝓝 0)) (hG : Secured (f ∘ tilt u) (K ∘ tilt u)) (hF : Secured f K) : stamp μ (K ∘ tilt u) (f ∘ tilt u) v=stamp μ K f v := by
  funext k
  obtain ⟨C,hC,h⟩:= tilt_stamp_le μ u v hF hG k rfl rfl he
  obtain ⟨D,hD,h'⟩:= tilt_stamp_le μ (-u) v hG hF k (passes rfl) (passes rfl) (by simpa using! he.neg)
  refine concord _ _ k ⟨C+D,by positivity,?_⟩ k le_rfl
  filter_upwards [h,h',eventually_pos] with t hx hy ht; rw [Real.norm_eq_abs,Pi.sub_apply,abs_le]
  constructor <;> nlinarith only [hx,hy,mul_nonneg hC (pow_nonneg ht.le (k+1)),mul_nonneg hD (pow_nonneg ht.le (k+1))]
end YM.RGComparison.Core16.Therm
