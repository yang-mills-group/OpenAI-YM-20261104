import YM.Pert.Scale.Curve
/-! Uniform leading-order comparison on a fixed compact positive length-ratio window about the measurement sequence. Input kernels are smooth only off diagonals. Includes the first length derivative; no formal analyticity in a varying coupling assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 160000
noncomputable section
namespace YM.Pert.Scale
open Analysis Filter Topology Set Function MeasureTheory Next.UVStress
open scoped ContDiff BigOperators
variable {n : ℕ}

structure Follows (f : ℕ → Points n → ℂ) (g : Points n → ℂ) : Prop where
  actual (k : ℕ) : ContDiffOn ℝ ∞ (f k) (conf n)
  lead : ContDiffOn ℝ ∞ g (conf n)
  jets (j) (K : Set (Points n)) (hk : IsCompact K) (hh : K⊆conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ x∈K, ‖iteratedFDeriv ℝ j (f k) x-iteratedFDeriv ℝ j g x‖ ≤ ε
variable {f : ℕ → Points n → ℂ} {g : Points n → ℂ} (h : Follows f g)

include h in
private lemma together (t : Test n) {s : ℝ} (hs : 0<s) (j : ℕ) {ε : ℝ} (he : 0<ε) :
   ∀ᶠ i : ℕ×ℝ in atTop ×ˢ 𝓝 s, ∀ x∈tsupport t, ‖iteratedFDeriv ℝ j (f i.1) (i.2•x) - iteratedFDeriv ℝ j g (i.2•x)‖ ≤ ε := by
  haveI : IsBoundedSMul ℝ (Points n) := .of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
  let J := Icc (s/2) (2*s)
  have hJ : J∈𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  let A := fun i:ℝ × Points n => i.1 • i.2
  let K := A '' (J ×ˢ tsupport t)
  have hk : IsCompact K := (isCompact_Icc.prod t.hasCompactSupport).image (show Continuous A from continuous_fst.smul continuous_snd)
  have hp : K⊆conf n := by
    rintro _ ⟨⟨u,x⟩, ⟨hu,hx⟩,rfl⟩; exact slides (lt_of_lt_of_le (by linarith) hu.1) (t.tsupport_subset hx)
  exact ((h.jets j K hk hp ε he).prod_mk (show ∀ᶠ u in 𝓝 s,u∈J from hJ)).mono (fun i hi x hx =>
        hi.1 _ ⟨(i.2,x),⟨hi.2,hx⟩,rfl⟩)

private lemma test_compare {ι : Type} {l : Filter ι} (t : Test n) (v q : ι → Points n → ℂ)
   (hv : ∀ᶠ i in l, ContinuousOn (v i) (conf n)) (hq : ∀ᶠ i in l, ContinuousOn (q i) (conf n))
   (he : ∀ δ : ℝ,0<δ → ∀ᶠ i in l,∀ x∈ tsupport t, ‖(v i-q i) x‖ ≤ δ) :
     Tendsto (fun i=>t.applyTo (v i) - t.applyTo (q i)) l (𝓝 0) := by
  have hi : Integrable (fun x => ‖t x‖) := (t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).norm
  refine Metric.tendsto_nhds.mpr fun ε hw => ?_
  let N := ∫ x, ‖t x‖
  have nn : 0≤N := integral_nonneg (fun _=> norm_nonneg _)
  let δ := ε/(N+1)
  have hd : 0<δ := div_pos hw (by linarith)
  filter_upwards [hv,hq,he _ hd] with i hp hr hi'
  have hh : ∀ x, ‖t x * (v i-q i) x‖ ≤ ‖t x‖ * δ := fun x=> by
    by_cases hx : x∈ tsupport t
    · grw [norm_mul_le _ _,hi' _ hx]
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [dist_zero_right,← test_sub _ _ hp hr]
  have h' := (norm_integral_le_integral_norm (fun x=> t x*(v i-q i) x)).trans (integral_mono (t.smearing (hp.sub hr) |>.norm) (hi.mul_const δ) hh)
  rw [integral_mul_const] at h'
  apply h'.trans_lt
  calc
     N * (ε/(N+1)) = (N/(N+1))*ε := by ring
     _ < 1*ε := mul_lt_mul_of_pos_right ((div_lt_one (by positivity)).mpr (by linarith)) hw
     _ = _ := one_mul _

namespace Follows
include h
theorem value (t : Test n) {s : ℝ} (hs : 0<s) :
    Tendsto (fun i : ℕ×ℝ => shiftMean t (f i.1) i.2) (atTop ×ˢ 𝓝 s) (𝓝 (shiftMean t g s)) := by
  haveI : IsBoundedSMul ℝ (Points n) := .of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
  have hp {v : Points n → ℂ} (hv : ContDiffOn ℝ ∞ v (conf n)) {w : ℝ} (hw : 0<w) :
       ContinuousOn (fun x => v (w • x)) (conf n) := hv.continuousOn.comp (ContinuousOn.const_smul continuousOn_id w) (fun _=>slides hw)
  have hw := (show ∀ᶠ w in 𝓝 s, 0<w from lt_mem_nhds hs).prod_inr (atTop (α:=ℕ))
  have he : Tendsto (fun i : ℕ×ℝ => shiftMean t (f i.1) i.2 - shiftMean t g i.2) (atTop ×ˢ 𝓝 s) (𝓝 0) := by
    apply test_compare t (fun i x => f i.1 (i.2•x)) (fun i x=> g (i.2•x)) (hw.mono fun i hi=>hp (h.actual i.1) hi) (hw.mono fun _ hi => hp h.lead hi)
    exact fun δ hd => (together h t hs 0 hd).mono fun i hi x hx => by
      change ‖(f i.1-g) (i.2•x)‖≤δ
      rw [← norm_iteratedFDeriv_zero (𝕜:=ℝ) (f:=f i.1-g) (x:=i.2•x), show iteratedFDeriv ℝ 0 (f i.1-g) (i.2•x) = iteratedFDeriv ℝ 0 (f i.1) (i.2•x)-iteratedFDeriv ℝ 0 g (i.2•x) from ContinuousMultilinearMap.ext fun _=>rfl]
      exact hi x hx
  have hv : Tendsto (fun i: ℕ×ℝ =>shiftMean t g i.2) (atTop ×ˢ 𝓝 s) (𝓝 (shiftMean t g s)) := (shift_deriv t h.lead hs).continuousAt.tendsto.comp tendsto_snd
  simpa only [zero_add,Function.comp_apply,sub_add_cancel] using he.add hv

private lemma first_uniform (t : Test n) {s : ℝ} (hs : 0<s) (δ) (hd : 0<δ) :
   ∀ᶠ i : ℕ×ℝ in atTop ×ˢ 𝓝 s,∀ x∈tsupport t, ‖fderiv ℝ (f i.1) (i.2•x) x-fderiv ℝ g (i.2•x) x‖ ≤ δ := by
  obtain ⟨c,hc⟩ := t.hasCompactSupport.exists_bound_of_continuousOn (f:=id) continuousOn_id
  let v := δ/(|c|+1)
  filter_upwards [together h t hs 1 (ε:=v) (div_pos hd (by positivity))] with i hi x hx
  let A := iteratedFDeriv ℝ 1 (f i.1) (i.2•x)-iteratedFDeriv ℝ 1 g (i.2•x)
  have hv : 0<v := div_pos hd (by positivity)
  have H : v * |c| ≤ δ :=
      (mul_le_mul_of_nonneg_left (show |c| ≤ |c|+1 by linarith) hv.le).trans_eq (div_mul_cancel₀ _ (by positivity))
  have hop := A.le_opNorm (fun _=>x)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one] at hop
  simpa only [A,ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply] using hop.trans ((mul_le_mul (show ‖A‖≤v from hi x hx) (show ‖x‖≤|c| from (hc x hx).trans (le_abs_self c)) (norm_nonneg _) hv.le).trans H)
theorem slope (t : Test n) {s : ℝ} (hs : 0<s) :
    Tendsto (fun k : ℕ => deriv (shiftMean t (f k)) s) atTop (𝓝 (deriv (shiftMean t g) s)) := by
  simp_rw [(shift_deriv t h.lead hs).deriv,(shift_deriv t (h.actual _) hs).deriv]
  haveI : IsBoundedSMul ℝ (Points n) := .of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
  let A (v : Points n→ℂ) (x:Points n) := fderiv ℝ v (s•x) x
  refine Position.paired_limit t (F:=fun i x=>A (f i) x) (G:=A g) ?_ ?_ (fun δ hd=> ?_)
  · intro i x hx; exact (((slides_term hs (f i) (h.actual i) hx).comp (f:=fun x : Points n=>s•x) (by fun_prop)).clm_apply continuousAt_id).continuousWithinAt
  · intro x hx; exact (((slides_term hs g h.lead hx).comp (f:=fun x : Points n=>s•x) (by fun_prop)).clm_apply continuousAt_id).continuousWithinAt
  have he : Tendsto (fun k : ℕ => (k,s)) atTop (atTop ×ˢ 𝓝 s) := tendsto_id.prodMk tendsto_const_nhds
  exact he.eventually (first_uniform h t hs δ hd)
end Follows
end YM.Pert.Scale
