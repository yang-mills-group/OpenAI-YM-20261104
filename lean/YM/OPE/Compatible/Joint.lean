import YM.OPE.Compatible.Mixtures

/-!
# Uniform point and arbitrary joint-test bound wrappers

On compact permitted geometry can integrate with bounded total mass in *all*
positions, not only monomial fields. Allow complex weights (L1 against the
given measure) with constant exactly their L1 mass. A compact may itself
be the test parameter space; coordinates need only be continuous so every
finite measure supported on such a geometry is allowed. Constants in the
rate conclusions won't depend on these parameters or measure family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table MeasureTheory Survey OS OS.Ground
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (U : Spec.Final C f S)
variable {I J B:Type} [Fintype I] [Fintype J]

/-- Kernel level on true words in all states. Internally the operator-norm
estimate on their ground algebra element. -/
structure Seen (k : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) (y : J → E4) (q : J → S.Tag)
    (ε : ℝ) : Prop where
  visible : Covered S r x o
  exterior : Injective (beside x y)
  centered : Injective (beside (sole o) y)
  price : ‖drift U k r x p o y q‖ ≤ ε

section point
variable {U} {k : ℕ} {r ε : ℝ} {x : I → E4} {p : I → S.Tag} {o : E4} {y : J → E4}
    {q : J → S.Tag} (h : Seen U k r x p o y q ε)
include h
lemma Seen.characters (i : Viewers U) :
    ‖kernel (spectator U i) (beside x y) (beside p q) -
      Cov.insert S (spectator U i) o y q k (trunc U k r x p o)‖ ≤ ε := by
  rw [← drift_reveals U k r x p o y q h.exterior h.centered i]
  exact (glance_bound U i _).trans h.price
/-- Thus for any probability mixture (in particular also delta measures).
This also controls a convex combination with the unselected hierarchy;
that hierarchy is already the distinguished barycenter on these words. -/
lemma Seen.any (μ : Measure U.α.space.X) [IsProbabilityMeasure μ] :
    ‖(∫ i, kernel (spectator U (some i)) (beside x y) (beside p q) ∂μ) -
      ∑ a∈ shades (facets U) k, beam U a r x p o *
        ∫ i, kernel (spectator U (some i)) (beside (sole o) y) (beside (sole (title U a)) q) ∂μ‖ ≤ ε := by
  rw [← drift_blend U μ k r x p o y q h.exterior h.centered]; exact (blend_bound U μ _).trans h.price
end point

-- compact metric spaces needed (integrate, projection topology).
section
variable [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] (μ : Measure B)
  (φ:B→ℂ)

omit [TopologicalSpace B] [BorelSpace B] [CompactSpace B] [SecondCountableTopology B] in
lemma within_price {X:Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X]
    {p:B→X} (hp : AEStronglyMeasurable p μ) {C:ℝ} (hφ : Integrable φ μ)
    (h : ∀ y, ‖p y‖ ≤ C) : Integrable (fun y => φ y • p y) μ ∧
      ‖∫ y, φ y • p y ∂μ‖ ≤ C*(∫ y,‖φ y‖ ∂μ) := by
  have he : ∀ᵐ y ∂μ, ‖φ y • p y‖ ≤ C*‖φ y‖ := Eventually.of_forall fun y => by
    rw [norm_smul,mul_comm C]; exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)
  have hh := hφ.norm.const_mul C
  exact ⟨hh.mono' (hφ.aestronglyMeasurable.smul hp) he,
    (norm_integral_le_of_norm_le hh he).trans (integral_const_mul ..).le⟩

private lemma bounded_weights {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X]
    (p:B→ X) (hp:Continuous p) (hφ: Integrable φ μ) : Integrable (fun x=> φ x • p x) μ := by
  obtain ⟨A,hA⟩ := isCompact_univ.exists_bound_of_continuousOn hp.continuousOn
  exact (within_price μ φ hp.aestronglyMeasurable hφ fun y => hA y (mem_univ _)).1

omit [TopologicalSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B] in
private lemma packed {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G:B→X} {ι:Type} {v:ι→B→X} (S:Finset ι) (h : Integrable G μ) (he : ∀ i, Integrable (v i) μ) :
    Integrable (fun b => G b - ∑ i∈ S,v i b) μ ∧
    (∫ b,G b ∂μ) - (∑ i∈ S, ∫ b,v i b ∂μ) = (∫ b,G b-∑ i∈ S,v i b ∂μ) := by
  constructor
  · exact Integrable.sub (μ:=μ) h (integrable_finsetSum S fun i _ => he i)
  rw [integral_sub h (integrable_finsetSum S fun i _ => he i),integral_finsetSum S fun i _ => he i]

private lemma downs {X:Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (r:ℂ) (t:X) :
    ‖r • t‖ ≤ ‖r‖ * ‖t‖ := (norm_smul ..).le
variable (k : ℕ) (r : ℝ) (x:B→I→E4)(o:B→E4) (y:B→J→E4) (p:I→S.Tag) (q:J→S.Tag)
    (a : Tones U) (u : ℝ)
    (hx:Continuous x) (ho:Continuous o) (hy:Continuous y)
    (h : ∀ b, Seen U k r (x b) p (o b) (y b) q u)
    (hφ: Integrable φ μ)

-- Lean needs help with inherited norm/metric structure for StarSubalgebra
local instance : ContinuousENorm (Round U:Type) := SeminormedAddGroup.toContinuousENorm (E:=(Round U:Type))

omit [TopologicalSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B] in
private lemma goesThrough (F : (Round U:Type) →L[ℂ] ℂ) (p:B→ Round U) (h:Integrable p μ) :
    F (∫ x, p x ∂μ) = ∫ x,F (p x) ∂μ := by
  exact ContinuousLinearMap.integral_comp_comm (E:=(Round U:Type)) (Fₗ:=ℂ) (𝕜:=ℂ) F (φ:=p) h|>.symm
/-- evaluation *term by term*, or can use the integral of drift
instead. All integral bounds apply to the same expression. -/
def totalReading : Round U :=
  (∫ b, φ b • object U (beside (x b) (y b)) (beside p q) ∂μ) -
    ∑ a∈ shades (facets U) k, ∫ b, φ b • signal U r (x b) p (o b) (y b) q a ∂μ
-- determine argument order: U μ φ k r x o y p q
include hx ho
omit [CompactSpace B] [SecondCountableTopology B] in
lemma joint_beam (he : ∀ b, Covered S r (x b) (o b)) (hu : ∀ b, ‖beam U a r (x b) p (o b)‖ ≤ u)
    (hφ : Integrable φ μ) : Integrable (fun b => φ b * beam U a r (x b) p (o b)) μ ∧
      ‖∫ b,φ b * beam U a r (x b) p (o b) ∂μ‖ ≤ u*(∫ b,‖φ b‖ ∂μ) := by
  have hc : Continuous fun b => beam U a r (x b) p (o b) := continuous_iff_continuousAt.mpr
    fun b => (beamSmooth U p (o b) (he b) a).continuousAt.comp
      (f:=fun b:B => (r,x b,o b)) (continuous_const.prodMk (hx.prodMk ho)).continuousAt
  exact within_price μ φ hc.aestronglyMeasurable hφ hu
include hy h hφ
lemma joint_family : Integrable (fun b => φ b • object U (beside (x b) (y b)) (beside p q)) μ ∧
    (∀ a, Integrable (fun b => φ b • signal U r (x b) p (o b) (y b) q a) μ) := by
  constructor
  · apply bounded_weights μ φ (fun b => object U (beside (x b) (y b)) (beside p q)) _ hφ
    have hv : Continuous fun b => beside (x b) (y b) := continuous_pi fun i => by
      rcases i with i | i
      exact continuous_pi_iff.mp hx i
      exact continuous_pi_iff.mp hy i
    apply continuous_iff_continuousAt.mpr
    intro i; exact (object_live U (beside (x i) (y i)) (h i).exterior (beside p q)).comp
      (f:=fun b => beside (x b) (y b)) hv.continuousAt
  intro a
  apply bounded_weights μ φ (fun b => signal U r (x b) p (o b) (y b) q a) _ hφ
  have hv : Continuous fun b => beside (sole (o b)) (y b) := continuous_pi fun i => by
    rcases i with i | i
    exact ho
    exact continuous_pi_iff.mp hy i
  apply continuous_iff_continuousAt.mpr
  intro i; unfold signal
  exact ((beamSmooth U p (o i) (h i).visible a).continuousAt.comp
    (f:=fun b => (r,x b,o b)) (continuous_const.prodMk (hx.prodMk ho)).continuousAt).smul
      ((object_live U (beside (sole (o i)) (y i)) (h i).centered _).comp
        (f:=fun b => beside (sole (o b)) (y b)) hv.continuousAt)
lemma joint_drift :
    Integrable (fun b => φ b • drift U k r (x b) p (o b) (y b) q) μ ∧
    totalReading U μ φ k r x o y p q = ∫ b, φ b • drift U k r (x b) p (o b) (y b) q ∂μ := by
  obtain ⟨hI,hF⟩ := joint_family U μ φ k r x o y p q u hx ho hy h hφ
  unfold totalReading
  simp_rw [drift, smul_sub, Finset.smul_sum]
  exact packed (X:=(Round U:Type)) μ (shades (facets U) k) (v:=fun a b => φ b • signal U r (x b) p (o b) (y b) q a) hI hF
lemma joint_price : ‖totalReading U μ φ k r x o y p q‖ ≤ u*(∫ y,‖φ y‖ ∂μ) := by
  obtain ⟨hI,hF⟩ := joint_drift U μ φ k r x o y p q u hx ho hy h hφ
  rw [hF]
  refine (norm_integral_le_of_norm_le (hφ.norm.const_mul u) (Eventually.of_forall fun b => ?_)).trans
    (integral_const_mul ..).le
  exact (downs (φ b) (drift U k r (x b) p (o b) (y b) q)).trans ((mul_le_mul_of_nonneg_left (h b).price (norm_nonneg _)).trans_eq (mul_comm ..))

lemma through_mix (ν : Measure U.α.space.X) [IsProbabilityMeasure ν] :
  blend U ν (totalReading U μ φ k r x o y p q) = (∫ b, φ b *
      (∫ i, kernel (spectator U (some i)) (beside (x b) (y b)) (beside p q) ∂ν) ∂μ) -
    ∑ a∈ shades (facets U) k, ∫ b, φ b * (beam U a r (x b) p (o b) *
      ∫ i, kernel (spectator U (some i)) (beside (sole (o b)) (y b))
        (beside (sole (title U a)) q) ∂ν) ∂μ := by
  obtain ⟨hI,hF⟩ := joint_family U μ φ k r x o y p q u hx ho hy h hφ
  unfold totalReading
  rw [map_sub,map_sum,goesThrough U μ (blend U ν) _ hI]; simp_rw [fun i =>
    goesThrough U μ (blend U ν) _ (hF i)]
  simp_rw [signal,map_smul,fun b => blend_kernel U ν _ (beside p q) (h b).exterior,
    fun b a => blend_kernel U ν _ (beside (sole (title U a)) q) (h b).centered]; rfl
lemma through_character (v : Viewers U) : glance U v (totalReading U μ φ k r x o y p q) =
    (∫ b, φ b * kernel (spectator U v) (beside (x b) (y b)) (beside p q) ∂μ) -
      ∑ a∈ shades (facets U) k, ∫ b, φ b * (beam U a r (x b) p (o b) *
        kernel (spectator U v) (beside (sole (o b)) (y b)) (beside (sole (title U a)) q)) ∂μ := by
  obtain ⟨hI,hF⟩ := joint_family U μ φ k r x o y p q u hx ho hy h hφ
  let K : (Round U:Type) →L[ℂ] ℂ := LinearMap.mkContinuous (E:=(Round U:Type)) (𝕜:=ℂ) (𝕜₂:=ℂ) (F:=ℂ) (glance U v) 1 (fun a => one_mul ‖a‖ |>.symm ▸ glance_bound U v a)
  change K _ = _
  unfold totalReading
  rw [map_sub, map_sum, goesThrough U μ K _ hI]; simp_rw [fun i => goesThrough U μ K _ (hF i)]; simp only [map_smul,signal]
  simp only [K, LinearMap.mkContinuous_apply]; simp_rw [fun b => object_sees U v _ (beside p q) (h b).exterior,fun b a => object_sees U v _ (beside (sole (title U a)) q) (h b).centered]; rfl
end
end YM.OPE.Cov.Display
