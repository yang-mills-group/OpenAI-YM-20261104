import YM.LocalTaylorR2.Exponent.Pride
/-! # Tests on true geometry of the gauge step. May remove profiles at
 full support, including curvature and derivative paths. Doesn't assert
 any estimate on doing so. Price is separately estimated along Scalp.
 Burst adapts Port.Kept algebra to polynomial growth. -/
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

open Exponent
def towerScale (S:StepData c f) (Z:Support c) (B:ℕ) (a: Forest S.ratio) (z:a.Slice G × Air f G):= 1+‖Pond.swim (podium S G Z B) z.2‖
lemma towerMax (U:Support c)(B:ℕ)(z: F.Slice G × Air f G):1≤towerScale S U B F z:= by unfold towerScale; linarith [norm_nonneg (swim (podium S G U B) z.2)]
structure Burst (H : Cash W s μ L Q o C T R) (U : Support c) (K : Test T) : Prop where
  links : ∀ (F:Forest S.ratio) (X X':Coat T F) (w v:Air f G), X.x=s → X.width=o.K →
    ∀ Z:Support c, U⊆Z → Village X X' Z → Pond.swim (podium S G Z X.B) w=Pond.swim (podium S G Z X.B) v → K F X w=K F X' v
  borel : ∀ (E:Type) [MeasurableSpace E] (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K →
    ∀ (V:E→ Config G c) (Y:E→ F.Slice G) (w:E→ Air f G), Measurable V → Measurable Y → Measurable w →
    Measurable fun t=> K F (Art.drive X (V t) (Y t)) (w t)
  rotate : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → Hue X → ∀ z:Site c→ G.El,∀ w:Air f G, K F (sluice X z) (weep X z w)=K F X w
  clutch : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → X.manifest →
    ∀ (j:ℕ) (b A:ℝ) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V:E→ Config G c) (x:E),
    Glass P X V x j W → Canary G b A → 8*o.a*Pressure.fiery G s L ≤ b/2 →
    ∀ Z:Support c,U⊆Z → Drifts (towerScale S Z X.B F) (fun (t:F.Slice G×Air f G) y=> K F (vary (X.wrapY t.1) (V y)) (course (X.wrapY t.1) b R.beta t.2 (V y))) x j

namespace Burst
variable {U:Support c} {K K' : Test T}

lemma mono (h:Burst H U K) {V} (hU:U⊆V) : Burst H V K :=
  ⟨fun F X X' w v hh h' Z hZ=> h.links F X X' w v hh h' Z (hU.trans hZ),h.borel,h.rotate,fun F X hx hX hu m b A E _ _ _ V x hQ hv hz Y hY=> h.clutch F X hx hX hu m b A E V x hQ hv hz Y (Subset.trans hU hY)⟩
lemma fixed (x:ℝ) : Burst H U (fun _ _ _=>x) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _=> rfl, fun _ _ _ _ _ _ _ _ _ _ _ _=> measurable_const,
    fun _ _ _ _ _ _ _=> rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=> Drifts.fat (Zest.still _)⟩
lemma times (h:Burst H U K) (h':Burst H U K') : Burst H U (fun F X w=> K F X w*K' F X w) := by
  constructor
  · intro F X X' w v hx hX Z hv hp hl
    exact congr_arg₂ (·*·) (h.links F X X' w v hx hX Z hv hp hl) (h'.links F X X' w v hx hX Z hv hp hl)
  · intro _ _ F X hx hX V Y w hp he ht
    exact (h.borel _ _ _ hx hX _ _ _ hp he ht).mul (h'.borel _ _ _ hx hX _ _ _ hp he ht)
  · intro F X hx hX hΨ z w; rw [h.rotate F X hx hX hΨ z w,h'.rotate F X hx hX hΨ z w]
  intro F X hx hX he j b d E _ _ _ V x hp ht hw Z hZ
  exact (h.clutch F X hx hX he j b d E V x hp ht hw Z hZ).twins (ContinuousLinearMap.mul ℝ ℝ)
    (h'.clutch F X hx hX he j b d E V x hp ht hw Z hZ)
lemma plus (h:Burst H U K) (h':Burst H U K') : Burst H U (fun F X w=> K F X w+K' F X w) :=by
  constructor
  · intro F X X' w v hx hX Z hv hp hl; rw [h.links F X X' w v hx hX Z hv hp hl,h'.links F X X' w v hx hX Z hv hp hl]
  · intro _ _ F X hx hX V Y w hp he ht; exact (h.borel _ _ _ hx hX _ _ _ hp he ht).add (h'.borel _ _ _ hx hX _ _ _ hp he ht)
  · intro F X hx hX hΨ z w; rw [h.rotate F X hx hX hΨ z w,h'.rotate F X hx hX hΨ z w]
  intro F X hx hX he j b d E _ _ _ V x hp ht hw Z hZ
  exact Drifts.more (towerMax Z X.B (F:=F)) (h.clutch F X hx hX he j b d E V x hp ht hw Z hZ) (h'.clutch F X hx hX he j b d E V x hp ht hw Z hZ)
lemma congrBody (h:Burst H U K) (p : ∀ F X w, K F X w=K' F X w) : Burst H U K':=by
  rw [show K'=K from (funext fun F=>funext fun X=>funext fun w=>p F X w).symm]; exact h
lemma fat (h:Kept H U K): Burst H U K:= ⟨h.links,h.borel,h.rotate,fun F X s v hu m b A E _ _ _ V x hp ht hw _ _=> Drifts.fat (h.clutch F X s v hu m b A E V x hp ht hw)⟩
lemma sub (h:Burst H U K) (h':Burst H U K') : Burst H U (fun F X w=> K F X w-K' F X w) := (h.plus ((Burst.fixed (-1)).times h')).congrBody (fun F X w=> by ring)
lemma product {ι:Type*} (V:Finset ι) (f:ι→Test T) (h:∀ i∈V,Burst H U (f i)) : Burst H U (fun F X w=> ∏ i∈V, f i F X w) := by
  induction V using Finset.induction_on with
  | empty => simp only [prod_empty]; exact fixed _
  | insert i V hh hi =>
    simp_rw [prod_insert hh]; exact (h i (mem_insert_self ..)).times (hi fun j hj=> h j (mem_insert_of_mem hj))
end Burst
end YM.LocalTaylorR2.Port
