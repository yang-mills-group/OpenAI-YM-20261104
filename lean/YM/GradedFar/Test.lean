import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import YM.GradedFar.Penultimate
import Mathlib.MeasureTheory.VectorMeasure.Integral
/-!
# Test interface

Use the very same joint profile for all terms, including the Near shape in the response term
(for the FarCoefficients evaluation). Histograms, point measurements, or smear both shapes: don't
need a product measure hypothesis. State also for continuous profiles priced on larger space X
so in an application one can for example keep a center parameter too (not used by these formal
comparison kernels). Use complex tests (`B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ` the ordinary multiplication) or
real signed tests and variations thereof.

No change of variables is used. In particular these measures **already live** in x,y variables;
not integrating in (x,Ty) against a spoofed unscaled test. Note: pointwise theorem doesn't
apply test-price of `Match` for UV mesh (that has own support/norm requirements).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries MeasureTheory
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {A : Arenas G} {F : ℝ → Frames G} {ψ : ℝ → PowerSeries ℂ}
    (H : Canon.Physical A ψ F) (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    {X : Type*} [TopologicalSpace X] {x : X → Points n} {y : X → Points m} {η : ℝ}
    (hx : Continuous x) (hy : Continuous y)

include H hx hy

lemma continuous_full (hxy : ∀ i, forest (x i) (squeeze η (y i)) ∈ conf (n+m))
    (u : Inputs G d) (v : Inputs G e) (k : ℕ) :
    Continuous (fun i => coeff k (fullSeries A F η hd he (x i) (y i) u v)) := by
  simp_rw [fullSeries_near η hd he _ _ u v A F, fullSeries_far η hd he _ _ _ v A F, map_sum,
    coeff_C_mul, basisWord, fullSeries_expansion H.scope _ _ _ H.dimensions, map_sum, coeff_mul, map_sum, coeff_mul]
  have reach : Continuous (fun i : X => forest (x i) (squeeze η (y i))) :=
    (continual (f:=Prod.fst) (g:=Prod.snd) continuous_fst continuous_snd).comp
      (hx.prodMk (hy.const_smul (Real.exp (-η))))
  have hp (r : ℕ) (w : Scan G (n+m)) : Continuous (fun i => coeff r (install A _
      (forest (x i) (squeeze η (y i))) w)) := by
    apply continuous_iff_continuousAt.mpr; intro i
    let f j := forest (x j) (squeeze η (y j))
    have hf : ContinuousAt f i := reach.continuousAt
    exact ContinuousAt.comp (f:=f) ((H.awake _ w r).continuousAt ((conf_open _).mem_nhds (hxy i))) hf
  unfold party; fun_prop (disch:=aesop)

lemma continuous_pair (hin : ∀ i, x i ∈ conf n) (hxy : ∀ i, forest (x i) (squeeze η (y i)) ∈ conf (n+m))
    (hout : ∀ i, y i ∈ Outside m) (u : Inputs G d) (v : Inputs G e) (p : ℕ) (z : ℝ) :
    Continuous (fun i => crop p z (fullSeries A F η hd he (x i) (y i) u v)) ∧
    Continuous (fun i => croppedResponse A F η hh he (y i) v p z (croppedVector A h p u (x i) z)) := by
  have hv : ∀ a : Toon G h, Continuous (fun i => crop p z (ope A u (x i) (Dframe.flash a))) := by
    intro a
    have hf (j : ℕ) (q : Scan G n) : Continuous (fun i => coeff j (Canon.FarCoefficients A q (x i) (Dframe.flash a))) := by
      apply continuous_iff_continuousAt.mpr; intro i
      exact (((H.far q).2.1 _ j).continuousAt ((conf_open n).mem_nhds (hin i))).comp hx.continuousAt
    simp_rw [crop_eq, ope, map_sum, coeff_C_mul]; fun_prop
  have hc {n' : ℕ} {d' : Fin n' → ℕ} {x' : X → Points n'} (hd' : Through l d') (hx' : Continuous x')
      (hi : ∀ i, forest (x' i) (squeeze η (y i)) ∈ conf (n'+m)) (u' : Inputs G d') :
      Continuous (fun i => crop p z (fullSeries A F η hd' he (x' i) (y i) u' v)) := by
    simp_rw [crop_eq]; exact continuous_finsetSum _ fun j _ => (continuous_full H hd' he hx' hy hi u' v j).const_mul _
  refine ⟨hc hd hx hxy u,?_⟩
  simp_rw [croppedVector, map_sum, _root_.map_smul, croppedResponse_apply, smul_eq_mul]; apply continuous_finsetSum
  intro a _; refine (hv a).mul ?_
  exact hc (x':=fun _ => (0 : Points 1)) (d':=Output h) (fun _ => hh) continuous_const
    (fun i => lives η (hout i)) _

omit H hx hy

-- usable also for a later physical/subtraction comparison.
theorem test_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (μ : VectorMeasure X E) [IsFiniteMeasure μ.variation]
    (B : ℂ →L[ℝ] E →L[ℝ] ℂ) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    {C : ℝ} (h : ∀ i, ‖f i-g i‖ ≤ C) :
    μ.Integrable f ∧ μ.Integrable g ∧ ‖(∫ᵛ i, f i ∂[B; μ]) - (∫ᵛ i, g i ∂[B; μ])‖ ≤
      C * ‖B‖ * μ.variation.real univ := by
  have h1 : μ.Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h2 : μ.Integrable g := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  refine ⟨h1,h2,?_⟩
  rw [← VectorMeasure.integral_sub h1 h2]
  exact VectorMeasure.norm_integral_le_of_norm_le_const (Eventually.of_forall h)

include H hx hy
/-- Thus one can make the M2 comparison against both real signed and complex joint tests.
Use the SAME total variation on the unscaled joint compact, always. `B` can be
`ContinuousLinearMap.mul ℝ ℂ` (has opNorm ≤ 1), standard signed pairing multiplier etc. -/
theorem test_formal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (μ : VectorMeasure X E) [IsFiniteMeasure μ.variation]
    (B : ℂ →L[ℝ] E →L[ℝ] ℂ)
    (hin : ∀ i, x i ∈ conf n) (hxy : ∀ i, forest (x i) (squeeze η (y i)) ∈ conf (n+m))
    (hout : ∀ i, y i ∈ Outside m) (u : Inputs G d) (v : Inputs G e) (p : ℕ) (z : ℝ)
    {C : ℝ} (hb : ∀ i, ‖difference A F η hd he hh (x i) (y i) u v p z‖ ≤ C) :
    let Y := fun i => crop p z (fullSeries A F η hd he (x i) (y i) u v)
    let D := fun i => croppedResponse A F η hh he (y i) v p z (croppedVector A h p u (x i) z)
    μ.Integrable Y ∧ μ.Integrable D ∧
      ‖(∫ᵛ i, Y i ∂[B; μ]) - (∫ᵛ i, D i ∂[B; μ])‖ ≤ C * ‖B‖ * μ.variation.real univ := by
  obtain ⟨hy,hd⟩ := continuous_pair H hd he hh hx hy hin hxy hout u v p z
  exact test_difference μ B hy hd hb
end YM.FVA2.GradedFar


/-! A price on a compact set can be paid inside the same joint measure. We use
actual integrals, allow arbitrary variation-finite vector measures on the compacta (in
particular signed measures), and no independence of coordinates.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Set MeasureTheory VectorMeasure
open scoped Topology

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The RHS has the actual total variation of the test. No dummy value of
integrals used: compact continuity and finite variation entail integrability. -/
theorem pair_integral (φ : VectorMeasure X E) [IsFiniteMeasure φ.variation]
    (B : ℂ →L[ℝ] E →L[ℝ] ℂ) {F Q : X → ℂ} (hF : Continuous F) (hQ : Continuous Q)
    (C : ℝ) (h : ∀ x, ‖F x-Q x‖ ≤ C) :
    φ.Integrable F ∧ φ.Integrable Q ∧
    ‖(∫ᵛ x, F x ∂[B; φ]) - (∫ᵛ x, Q x ∂[B; φ])‖ ≤ C * ‖B‖ * φ.variation.real univ := by
  have hf : φ.Integrable F := hF.integrable_of_hasCompactSupport (.of_compactSpace F)
  have hq : φ.Integrable Q := hQ.integrable_of_hasCompactSupport (.of_compactSpace Q)
  refine ⟨hf,hq,?_⟩
  rw [← integral_fun_sub hf hq]
  exact VectorMeasure.norm_integral_le_of_norm_le_const (f:=fun x => F x - Q x) (Eventually.of_forall h)
end
end YM.FVA2.GradedFar
