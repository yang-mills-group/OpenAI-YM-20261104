import YM.SchemeConversionRG11.Maxwell.MeanSpan

/-! # Compact extraction from real probes' polynomial moments. Use peaks (no
assertion about complex orbits). -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Tensor Set MvPolynomial
open scoped Topology BigOperators RealInnerProductSpace ComplexOrder

variable {ι : Type} [Fintype ι] {v : Bean ι} {r : ℝ}

lemma peak {a b : Bean ι→ℝ} (ha : Continuous a) (hb : Continuous b) (uv : v∈ ball (0:Bean ι) r) (hA : 1<a v)
    (haP : ∀ z∈closedBall (0:Bean ι) r,0≤a z) (hbP : ∀ z∈closedBall (0:Bean ι) r,0≤b z ∧ b z≤1)
    (hp : ∀ k : ℕ,(∫ x in closedBall (0:Bean ι) r,a x^k)=(∫ x in closedBall (0:Bean ι) r,b x^k)) : False := by
  classical
  obtain ⟨θ,hθ,hy⟩ := exists_between hA
  let B := closedBall (0:Bean ι) r
  have he : (B ∩ {x|θ<a x}) ∈ 𝓝 v := inter_mem (mem_of_superset (isOpen_ball.mem_nhds uv) ball_subset_closedBall) ((isOpen_lt continuous_const ha).mem_nhds hy)
  obtain ⟨R,hR,hH⟩ := nhds_basis_closedBall.mem_iff.mp he
  let K := closedBall v R
  have hi : K ⊆ B := subset_trans hH inter_subset_left
  have hJ : 0<volume.real K := ENNReal.toReal_pos (measure_closedBall_pos volume _ hR).ne' ((isCompact_closedBall v R).measure_lt_top (μ:=volume)).ne
  have hm : Tendsto (fun k : ℕ ↦ volume.real K*θ^k) atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt hθ).const_mul_atTop hJ
  obtain ⟨k,hk⟩ := (hm.eventually (eventually_gt_atTop (volume.real B))).exists
  refine not_le.mpr hk ?_
  calc
    volume.real K*θ^k=∫ _x in K, θ^k := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in K,a x^k := setIntegral_mono_on (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall ..))
        ((ha.pow k).continuousOn.integrableOn_compact (isCompact_closedBall ..)) measurableSet_closedBall (fun x hx ↦ pow_le_pow_left₀ (le_trans zero_le_one hθ.le) (le_of_lt (show θ<a x from (hH hx).2)) _)
    _ ≤ ∫ x in B,a x^k := by
      apply setIntegral_mono_set ((ha.pow k).continuousOn.integrableOn_compact (isCompact_closedBall ..)) ?_ (Eventually.of_forall (fun _ h ↦ hi h))
      filter_upwards [ae_restrict_mem (μ := volume) (s:=B) measurableSet_closedBall] with x hx; exact pow_nonneg (haP x hx) _
    _ = ∫ x in B,b x^k := hp _
    _ ≤ ∫ _x in B, (1:ℝ) := setIntegral_mono_on ((hb.pow k).continuousOn.integrableOn_compact (isCompact_closedBall ..))
        (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall ..)) measurableSet_closedBall (fun x hx ↦ by simpa using pow_le_pow_left₀ (hbP x hx).1 (hbP x hx).2 k)
    _ = volume.real B := by simp

lemma retrieve_point {f g : Bean ι→ℝ} (hf : Continuous f) (hg : Continuous g) (uv : v∈ ball (0:Bean ι) r) (hV : f v=0)
    (hG : ∀ z∈closedBall (0:Bean ι) r,0≤g z)
    (h : ∀ M T:ℝ,∀ k:ℕ,(∫ x in closedBall (0:Bean ι) r,(T*(M-f x))^k)=(∫ x in closedBall (0:Bean ι) r,(T*(M-g x))^k)) :
    ∃ z∈closedBall (0:Bean ι) r,g z=0 := by
  classical
  let B := closedBall (0:Bean ι) r
  by_contra! ht
  have hC : IsCompact B := isCompact_closedBall ..
  obtain ⟨w,hw,hmin⟩ := hC.exists_isMinOn ⟨v,ball_subset_closedBall uv⟩ hg.continuousOn
  have hW : 0<g w := lt_of_le_of_ne (hG _ hw) (Ne.symm (ht w hw))
  obtain ⟨m,hm⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨n,hn⟩ := hC.exists_bound_of_continuousOn hg.continuousOn
  let M := max m n+1
  have hF z (h : z∈B) : f z<M := by
    calc
      f z ≤ ‖f z‖ := le_abs_self _
      _ ≤ max m n := (hm _ h).trans (le_max_left ..)
      _ < M := lt_add_one _
  have hL z (h : z∈B) : g z<M := by
    calc
      g z ≤ ‖g z‖ := le_abs_self _
      _ ≤ max m n := (hn _ h).trans (le_max_right ..)
      _ < M := lt_add_one _
  let T := (M-g w)⁻¹
  let P : (Bean ι→ℝ) → (Bean ι→ℝ) := fun f z ↦ T*(M-f z)
  have hP (f : Bean ι→ℝ) (h : Continuous f) : Continuous (P f) := continuous_const.mul (continuous_const.sub h)
  have hT : 0<T := inv_pos.mpr (sub_pos.mpr (hL w hw))
  have he : 1=T*(M-g w) := Eq.symm (inv_mul_cancel₀ (sub_pos.mpr (hL w hw)).ne')
  exact peak (hP f hf) (hP g hg) uv (by unfold P; rw [he,hV]; exact mul_lt_mul_of_pos_left (by linarith) hT)
    (fun z hz ↦ (mul_pos hT (sub_pos.mpr (hF z hz))).le) (fun z hz ↦ ⟨(mul_pos hT (sub_pos.mpr (hL z hz))).le, by unfold P; rw [he]; gcongr; exact hmin hz⟩) (h M T)

variable {κ : Type*}

/-- real wall probe. -/
def retina (x : Bean ι) : ShellBook ι→ₐ[ℂ] ℂ := aeval fun i ↦ (x i:ℂ)
def realWall (p : ShellBook ι) := ∀ x, (↑((retina x p).re):ℂ)=retina x p

lemma glow (S : κ → ShellBook ι) (r : ℝ) (p : MvPolynomial κ ℂ) :
    mean ι r (aeval S p)=∫ x in closedBall (0:Bean ι) r, aeval (fun i ↦ retina x (S i)) p := by
  unfold mean
  change (∫ x in _,retina x (aeval S p))=_
  have ht (x : Bean ι) : (retina x).comp (aeval S)= aeval (fun i ↦ retina x (S i)) := by ext i; rw [AlgHom.comp_apply,aeval_X,aeval_X]
  simp_rw [← AlgHom.comp_apply,ht]

def wallTest (u : Finset κ) (f : κ→ℝ) (M T : ℝ) : MvPolynomial κ ℂ := C (T:ℂ) * (C (M:ℂ)-∑ i∈u,(X i-C (f i:ℂ))^2)

def squeak (u : Finset κ) (f : κ→ℝ) (S : κ → ShellBook ι) (x : Bean ι) := ∑ i∈u,((retina x (S i)).re-f i)^2

lemma continuous_squeak (u : Finset κ) (f : κ→ℝ) (S : κ → ShellBook ι) : Continuous (squeak u f S) := by
  refine continuous_finsetSum u fun i _ ↦ ?_; exact (((Complex.continuous_re.comp (meanable (S i))).sub continuous_const).pow 2)
lemma lamp (S : κ→ShellBook ι) (h : ∀ i,realWall (S i)) (x : Bean ι) (u : Finset κ) (f : κ→ℝ) (M T : ℝ) : aeval (fun i ↦ retina x (S i)) (wallTest u f M T)= (↑(T*(M-squeak u f S x)):ℂ) := by
  simp only [squeak,wallTest,map_pow,map_mul,map_sub,map_sum,aeval_X,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,Complex.ofReal_sum, h _ x]
lemma projected (S : κ→ShellBook ι) (h : ∀ i,realWall (S i)) (r : ℝ) (u : Finset κ) (f : κ→ℝ) (M T : ℝ) (k : ℕ) :
    mean ι r (aeval S ((wallTest u f M T)^k)) = (↑(∫ x in closedBall (0:Bean ι) r,(T*(M-squeak u f S x))^k):ℂ) := by
  rw [glow]; simp_rw [map_pow, lamp S h, ← Complex.ofReal_pow, integral_complex_ofReal]

lemma coincides {S S' : κ→ShellBook ι} (uv : v∈ball (0:Bean ι) r)
    (h : ∀ i,realWall (S i)) (h' : ∀ i,realWall (S' i))
    (H : ∀ p : MvPolynomial κ ℂ, mean ι r (aeval S p)=mean ι r (aeval S' p)) : ∃ u∈closedBall (0:Bean ι) r, ∀ i : κ, retina u (S' i)=retina v (S i) := by
  classical
  let B : Set (Bean ι) := closedBall 0 r
  let f i := (retina v (S i)).re
  let U i := {b:Bean ι|(retina b (S' i)).re=f i}
  have he : (B ∩ ⋂ i,U i).Nonempty := by
    refine IsCompact.inter_iInter_nonempty (isCompact_closedBall ..) U
      (fun i ↦ isClosed_eq (Complex.continuous_re.comp (meanable _)) continuous_const) (fun s ↦ ?_)
    have ht (M T : ℝ) (k) := ((projected S h r s f M T k).symm.trans (H ((wallTest s f M T)^k))).trans (projected S' h' ..)
    have hP (z) : 0 ≤ squeak s f S' z := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    obtain ⟨z,hz,hL⟩ := retrieve_point (continuous_squeak s f S) (continuous_squeak s f S') uv (by simp [squeak,f]) (fun z _ ↦ hP z) (fun M T k ↦ Complex.ofReal_injective (ht M T k))
    refine ⟨z,hz,Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mpr fun hi ↦ ?_⟩
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (s:=s) (fun _ _ ↦ sq_nonneg _)).mp hL i hi
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hi)
  obtain ⟨z,hz,hu⟩ := he; refine ⟨z,hz,fun i ↦ (h' i z).symm.trans ((congr_arg ((↑):ℝ→ℂ) (show (retina z (S' i)).re=f i from Set.mem_iInter.mp hu i)).trans (h _ _))⟩
end YM.SchemeConversionRG11.Corona
