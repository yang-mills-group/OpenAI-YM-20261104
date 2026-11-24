import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel

/-!
# Insertion calculation on E6-local log ingredients

Test = function of the *same* tree, Haar, Gaussian data.
Kept: do not change masks, roots, tag or mark locations.
Qualitative hypotheses needed for integrating/multiplying parts of the
actual log vertices on their own (before purchases of sharp derivative
bounds). Zest for sanity on a neighborhood, **not used for the numerical
Taylor remainder**. `S`/`Cash` will be instantiated on actual step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}

abbrev Test (T : Tube G S) := ∀ F : Forest S.ratio, Coat T F → Air f G → ℝ

structure Kept (H : Cash W s μ L Q o C T R) (U : Support c) (K : Test T) : Prop where
  links : ∀ (F:Forest S.ratio) (X X':Coat T F) (w v:Air f G), X.x=s → X.width=o.K →
    ∀ Z:Support c, U⊆Z → Village X X' Z → Pond.swim (podium S G Z X.B) w=Pond.swim (podium S G Z X.B) v → K F X w=K F X' v
  borel : ∀ (E:Type) [MeasurableSpace E] (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K →
    ∀ (V:E→ Config G c) (Y:E→ F.Slice G) (w:E→ Air f G), Measurable V → Measurable Y → Measurable w →
    Measurable fun t=> K F (Art.drive X (V t) (Y t)) (w t)
  rotate : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → Hue X → ∀ z:Site c→ G.El,∀ w:Air f G, K F (sluice X z) (weep X z w)=K F X w
  clutch : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → X.manifest →
    ∀ (j:ℕ) (b A:ℝ) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V:E→ Config G c) (x:E),
    Glass P X V x j W → Canary G b A → 8*o.a*Pressure.fiery G s L ≤ b/2 →
    Zest (fun (t:F.Slice G×Air f G) y=> K F (vary (X.wrapY t.1) (V y)) (course (X.wrapY t.1) b R.beta t.2 (V y))) x j

namespace Kept
variable {U:Support c} {K K' : Test T}

lemma mono (h:Kept H U K) {V} (hU:U⊆V) : Kept H V K :=
  ⟨fun F X X' w v hh h' Z hZ=> h.links F X X' w v hh h' Z (hU.trans hZ),h.borel,h.rotate,h.clutch⟩
lemma fixed (x:ℝ) : Kept H U (fun _ _ _=>x) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _=> rfl, fun _ _ _ _ _ _ _ _ _ _ _ _=> measurable_const,
    fun _ _ _ _ _ _ _=> rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=> Zest.still _⟩
lemma times (h:Kept H U K) (h':Kept H U K') : Kept H U (fun F X w=> K F X w*K' F X w) := by
  constructor
  · intro F X X' w v hx hX Z hv hp hl
    exact congr_arg₂ (·*·) (h.links F X X' w v hx hX Z hv hp hl) (h'.links F X X' w v hx hX Z hv hp hl)
  · intro _ _ F X hx hX V Y w hp he ht
    exact (h.borel _ _ _ hx hX _ _ _ hp he ht).mul (h'.borel _ _ _ hx hX _ _ _ hp he ht)
  · intro F X hx hX hΨ z w; rw [h.rotate F X hx hX hΨ z w,h'.rotate F X hx hX hΨ z w]
  intro F X hx hX he j b d E _ _ _ V x hp ht hw
  exact (h.clutch F X hx hX he j b d E V x hp ht hw).paint
    (h'.clutch F X hx hX he j b d E V x hp ht hw)
lemma smooth (h:Kept H U K) (g:ℝ→ℝ) (hg:ContDiff ℝ ∞ g) : Kept H U (fun F X w=> g (K F X w)) := by
  constructor
  · intro F X X' w v hx hX Z hv hp hl; rw [h.links F X X' w v hx hX Z hv hp hl]
  · intro _ _ F X hx hX V Y w hp he ht
    exact hg.continuous.measurable.comp (h.borel _ _ _ hx hX _ _ _ hp he ht)
  · intro F X hx hX hΨ z w; rw [h.rotate F X hx hX hΨ z w]
  intro F X hx hX he j b d E _ _ _ V x hp ht hw
  exact (h.clutch F X hx hX he j b d E V x hp ht hw).wand (hg.of_le (WithTop.coe_le_coe.mpr le_top))
lemma product {ι:Type*} (V:Finset ι) (f:ι→Test T) (h:∀ i∈V,Kept H U (f i)) : Kept H U (fun F X w=> ∏ i∈V, f i F X w) := by
  induction V using Finset.induction_on with
  | empty => simp only [prod_empty]; exact fixed _
  | insert i V hh hi =>
    simp_rw [prod_insert hh]; exact (h i (mem_insert_self ..)).times (hi fun j hj=> h j (mem_insert_of_mem hj))
end Kept
end YM.LocalTaylorR2.Port
