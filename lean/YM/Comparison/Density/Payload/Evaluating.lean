import YM.Comparison.Density.Payload.Assembly
/-!
Finite-volume integrability of the complete assembled density, no rate
assertion. Also valid during reclosure before affine readjustment, etc.,
provided `Envelope` of the ACTUAL vacuum exponent used.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density
open Marker Testing Markers RG Lattice Function MeasureTheory Wilson Filter
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V}
scoped instance : NormedSpace ℝ (Poly R) := inferInstanceAs (NormedSpace ℝ (R.Mode → ℂ))
scoped instance : IsScalarTower ℝ ℂ (Poly R) := inferInstanceAs (IsScalarTower ℝ ℂ (R.Mode → ℂ))
-- These π instances define no submultiplicative norm.
variable {G : Gauge} {n : Side}
variable {X : V→Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable [Fintype V] {P : Rep G n} {Q : Assembly R X G n} {O : Readers V X n} {c b e k : ℝ} {w : V→ℝ}

namespace Assembly
variable (h : Q.Tidy P w O c b e k)
include h
lemma gauge_mask (x : Cross X) (H : GaugeInvariant P.exponent) : GaugeInvariant (Q.eval P x):= by
  intro i U; have hg : Q.exponent.log P.p x (Lattice.gauge i U) = Q.exponent.log P.p x U := by
    unfold Registers.log Registers.ledger; refine congrArg (Multi.lit R) (funext fun j=> congrArg₂ _ rfl ?_)
    apply tsum_congr; intro b; unfold Registers.supports
    by_cases he: Healthy P.p.threshold (Q.exponent.sites (j,b)) U
    · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ (by simpa only [Healthy, gauge_flags] using he)]; exact (h.layout.smooth _ _).symmetry ..
    rw [masked_ne _ _ _ _ he, masked_ne _ _ _ _ (by simpa only [Healthy, gauge_flags] using he)]
  simp only [Assembly.eval,hg,H i U]; refine congrArg₂ _ rfl ?_
  unfold mist; refine tsum_congr fun l=> ?_; unfold packet Activities.admissible; simp only [gauge_flags]; split; next _=> exact Finset.prod_congr rfl fun j _=> (h.carries x).sym j i U
  rfl

variable (hw : ∀ i,0<w i) (hk : 0≤e)
include hw hk
omit hk in
private lemma log_envelope (x : Cross X) : Envelope (Q.exponent.log P.p x) := by
  let A:= Q.exponent
  let g (j : R.Mode) (U : Config G n):= (A.log P.p x U).part j
  have he i : Envelope (g i) := by
    by_cases hk : i.val.Nonempty
    · let j : Multi.Hot R:= ⟨_,hk⟩
      have hq : g i = A.ledger P.p x j:= funext fun _=> Registers.alive _ _ j
      rw [hq]; obtain ⟨l,H⟩:= (Registers.dom hw h.layout h.growth x j).bound
      unfold Registers.ledger
      refine ⟨measurable_const.add (Measurable.tsum ?_),‖A.orderZero x j‖+l,fun v=> (norm_add_le ..).trans (add_le_add_right (H v) _)⟩
      intro i; exact masked_measurable _ _ _ (h.layout.smooth _ _).borel
    rw [show i=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hk)]; simp only [g,Registers.baseline]; exact ⟨measurable_const,0,fun _=>by simp⟩
  choose f H using fun i=> (he i).cost
  have hp (i : R.Mode): 0 ≤ f i := (norm_nonneg _).trans (H i 1)
  constructor
  · have hp: Measurable fun U : Config G n=> fun i => g i U := measurable_pi_lambda _ fun i=> (he i).meas
    rw [show inferInstanceAs (MeasurableSpace (R.Mode→ℂ))=borel (R.Mode→ℂ) from BorelSpace.measurable_eq] at hp
    exact hp
  refine ⟨∑ i,f i,fun U=>?_⟩
  change ‖(Q.exponent.log P.p x U).part‖≤ _
  exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _=> hp i)).mpr fun i=> (H i _).trans (Finset.single_le_sum (fun i _=> hp i) (Finset.mem_univ _))

lemma envelope (hz : Envelope P.exponent) (x : Cross X) : Envelope (Q.eval P x) := by
  have ha := log_envelope h hw x
  have hb : Envelope (mist P.p P.activities (Q.arms x)) := by
    refine ⟨Measurable.tsum ?_, (force_dom hw hk h x).bound⟩
    intro i; unfold packet; exact Measurable.ite (Activities.admissible_borel ..)
      (Finset.measurable_fun_prod _ fun i _=> (h.carries x).borel i) measurable_const
  constructor
  · exact (((embedded_cont.measurable.comp (Real.continuous_exp.measurable.comp hz.meas)).mul (Poly.pass_cont.measurable.comp ha.meas)).mul hb.meas)
  obtain ⟨v,hv⟩:= hz.cost; obtain ⟨u,hu⟩:= ha.cost; obtain ⟨y,hy⟩:= hb.cost
  let I := Set.Icc (-v) v; let J := Metric.closedBall (0: Poly R) u; let L:= Metric.closedBall (0:Poly R) y
  let f (z : (ℝ × Poly R) × Poly R) := magnify z.1.1 z.1.2 * z.2
  haveI : ProperSpace (Poly R) := inferInstanceAs (ProperSpace (R.Mode→ℂ))
  have he : Continuous (fun z=> ‖f z‖) := by
    apply Continuous.norm; unfold f magnify; have hc : Continuous (embedded R):= embedded_cont; fun_prop
  obtain ⟨B,H⟩:= (((isCompact_Icc (α:=ℝ) (a:=-v) (b:=v)).prod (isCompact_closedBall (0:Poly R) u) |>.prod (isCompact_closedBall (0:Poly R) y)).image he).bddAbove
  exact ⟨B,fun U=> H ⟨((P.exponent U,Q.exponent.log P.p x U),mist P.p P.activities (Q.arms x) U),
    ⟨⟨abs_le.mp (hv U),Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hu U)⟩,Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hy U)⟩,rfl⟩⟩

lemma integrable (hz : Envelope P.exponent) (x : Cross X) (μ : Measure (Config G n)) [IsFiniteMeasure μ] :
    Integrable (Q.eval P x) μ := by
  obtain ⟨hr,B,H⟩:= envelope h hw hk hz x
  exact Integrable.of_bound hr.aestronglyMeasurable B (Eventually.of_forall H)
end Assembly
end YM.Comparison.Density
