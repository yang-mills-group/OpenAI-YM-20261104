import YM.OPE.Frame.Mixed
/-!
# Bounded-mass joint measurements, kernels *only* used on fully separated loci

Use actual finite measure tests, or optionally complex densities in L¹ against them
(absolute-mass dependence). Arbitrary compact parameter spaces of scaled/unscaled
geometries with continuous projections. In particular arbitrary Borel masses on compact
sets of allowed center/x/y, no constraint that the measure factor into input and exterior
parts. Integrability applies to each term of the expansion separately, before doing
any asymptotics. Kernels of the cᵥ's use only the declared scale when composing. At each
scale a different joint measure may be used. Radius (and in nested uses every positive child
scale) fixed during the integration.
-/
set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Frame
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book} {F : Spec.Final C U S}
variable {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {y : J → E4} {r : ℝ} {o : E4} (μ : Audience F)
    (Z : Scheme F) (A : I → S.Tag) (B : J → S.Tag) (n : ℕ) {α : Type*} [MeasurableSpace α]
variable (ν : Measure α)

/-- Certifies integrable discrepancy (includes every point in stated geometry) and the
bound on its cost for all mass profiles, with threshold/constant independent of profile.
Absolute bound, so density costs only its L¹ norm. -/
structure Meets (K : ℝ) (f : α → ℂ) : Prop where
  live : Integrable f ν
  atmost (i) : ‖f i‖ ≤ K
namespace Meets
variable {f : α→ℂ}{K : ℝ}{ν}
lemma applies [IsFiniteMeasure ν] (H : Meets ν K f) : ‖∫ i, f i ∂ν‖ ≤ K * ν.real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall H.atmost)
lemma weighs (H : Meets ν K f) {w : α → ℂ} (h : Integrable w ν) : Integrable (fun i=> w i*f i) ν ∧
    ‖∫ i,w i*f i ∂ν‖ ≤ K*(∫ i,‖w i‖∂ν) := by
  refine ⟨h.mul_bdd H.live.aestronglyMeasurable (Eventually.of_forall H.atmost),?_⟩
  rw [← integral_const_mul]; exact norm_integral_le_of_norm_le (h.norm.const_mul _) (Eventually.of_forall fun i => by rw [norm_mul,mul_comm K]; exact mul_le_mul_of_nonneg_left (H.atmost i) (norm_nonneg _))
end Meets

variable [TopologicalSpace α] [CompactSpace α] [BorelSpace α] [IsFiniteMeasure ν]
variable {X : α → I → E4} {O : α → E4} {Y : α→ J → E4}
structure Supported (r : ℝ) (X : α→ I → E4) (O : α→ E4) : Prop where
  shape : Continuous X
  center : Continuous O
  domain (i:α) : Seen r (X i) (O i)
structure Fully (r : ℝ) (X : α → I → E4) (O : α→ E4) (Y : α→ J → E4) : Prop extends Supported r X O where
  profiles : Continuous Y
  live (i:α) : Injective (beside (X i) (Y i))
  pinned (i:α) : Injective (beside (sole (O i)) (Y i))

omit [Fintype I] [Fintype J] [MeasurableSpace α] [CompactSpace α] [BorelSpace α] in
lemma both_cont {Y:α→ J→E4} (h : Continuous X) (hY : Continuous Y) : Continuous (fun i:α => beside (X i) (Y i)) := by apply continuous_pi; intro a; rcases a with a|a; exacts [(continuous_apply a).comp h,(continuous_apply a).comp hY]

lemma joined_profile {f:α→ℂ} {K : ℝ} (h : Continuous f) (h' : ∀ i, ‖f i‖ ≤ K) : Meets ν K f := ⟨h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),h'⟩
namespace Scheme
variable (H : Services C U S)
omit H [CompactSpace α] [MeasurableSpace α] [BorelSpace α] in
lemma cCont (p : Row Z.rings) (h : Supported r X O) : Continuous (fun i=> Z.coeff r p A (X i) (O i)) := continuous_iff_continuousAt.mpr fun i=> (Z.smooth _ _ A (h.domain i)).continuousAt.comp (f:=fun i=> (r,X i,O i)) ((continuous_const.prodMk (h.shape.prodMk h.center)).continuousAt)
lemma cMeet (p : Row Z.rings) {K:ℝ} (h : Supported r X O) (hc : ∀ i, ‖Z.coeff r p A (X i) (O i)‖ ≤ K) : Meets ν K (fun i=> Z.coeff r p A (X i) (O i)) := joined_profile ν (Z.cCont A _ h) hc

include H
-- *Term by term* bona fide reading, useful also at fixed ratio
omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] in
lemma taken_cont (h : Fully r X O Y) : Continuous (fun i=> heard μ (beside (X i) (Y i)) (beside A B)) ∧
    ∀ p : Row Z.rings, Continuous (fun i=> Z.coeff r p A (X i) (O i) * heard μ (beside (sole (O i)) (Y i)) (beside (sole (Z.representation.label p)) B)) := by
  constructor
  · exact continuous_iff_continuousAt.mpr fun i=> (mix_cont _ μ H (h.live i)).comp (f := fun i=> beside (X i) (Y i)) (both_cont h.shape h.profiles).continuousAt
  intro p; apply Continuous.mul (Z.cCont ..); swap; exact h.toSupported -- h
  exact continuous_iff_continuousAt.mpr fun i=> (mix_cont _ μ H (h.pinned i)).comp (f := fun i=>beside (sole (O i)) (Y i)) (both_cont (continuous_pi fun _=> h.center) h.profiles).continuousAt
lemma captured (h : Fully r X O Y) : Integrable (fun i=> heard μ (beside (X i) (Y i)) (beside A B)) ν ∧
    ∀ p : Row Z.rings, Integrable (fun i=> Z.coeff r p A (X i) (O i) * heard μ (beside (sole (O i)) (Y i)) (beside (sole (Z.representation.label p)) B)) ν :=
  ⟨(Z.taken_cont μ A B H h).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), fun p=> ((Z.taken_cont μ A B H h).2 p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩
lemma play_cost_profile (h : Fully r X O Y) {K:ℝ} (hp : ∀ i:α, ‖Z.remainder n r A (X i) (O i) (Y i) B‖ ≤ K) : Meets ν K (fun i=> Z.play μ n r A (X i) (O i) (Y i) B) := by
  refine ⟨?_,fun i=> (Z.play_bound A B n μ (h.live i) (h.pinned i)).trans (hp i)⟩
  obtain ⟨ht,hb⟩:= Z.captured μ A B ν H h; exact ht.sub (integrable_finsetSum _ (fun i _=> hb i))
end Scheme
end YM.OPE.Frame
