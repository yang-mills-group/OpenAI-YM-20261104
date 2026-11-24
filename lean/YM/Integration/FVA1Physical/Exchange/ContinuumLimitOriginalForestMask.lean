import YM.Integration.FVA1Physical.Exchange.ContinuumLimitOriginalPhysicalVacuum
import YM.Comparison.RG02.Integral.Healthy

/-! The chart mask is defined on the forest slice. Sum the actual kernel
tags there before taking an absolute value. The fourth term of the local
comparison can then be priced under its own normalized physical law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OriginalMixedWilson
open Finset Filter Function MeasureTheory RG Wilson Gauge Precision Tree Lattice Exterior
open Next.SectorChange Comparison.RG02 Order Marker Multi
open Integral Actual Push.SectorMeasure
open scoped Topology BigOperators Classical
variable {G : Gauge} {I : Type} [DecidableEq I] {R : Census I} {c f : Side} {S : StepData c f}

/-- Original unnormalized masked push with the true source, without a
per-branch quota or a global smallness assumption for the mask. -/
def forestRead (F : Forest S.ratio) (β : ℝ) (V : Config G c)
    (D : Lit R (Config G f)) (A : Set (F.Slice G)) : Poly R :=
  charge (F.order G) (A.indicator (fun y => (S.density β (F.drape y) V:ℂ) • D (F.drape y)))

theorem forest_read_tags (F : Forest S.ratio) (β : ℝ) (V : Config G c)
    (ok : S.patch.Branches S.kernel G) (D : Lit R (Config G f))
    (admissible : Leaf.All D) (A : Set (F.Slice G)) (hm : MeasurableSet A) :
    forestRead F β V D A =
      ∑ t:S.Choices, charge (F.order G) (A.indicator (Actual.stack t V β D ∘ F.drape)) := by
  let ros := fun t:S.Choices => Actual.stack t V β D ∘ F.drape
  have rows : A.indicator (fun y => (S.density β (F.drape y) V:ℂ) • D (F.drape y)) =
      ∑ t:S.Choices,A.indicator (ros t) := by
    funext y
    by_cases h:y∈A
    · simp only [Set.indicator_of_mem h,Finset.sum_apply,ros,Function.comp_apply]
      have collected := congrFun (Actual.collective (S:=S) V β D) (F.drape y)
      simpa only [Finset.sum_apply] using collected
    · simp [h]
  unfold forestRead
  rw [rows]
  apply sum_cost
  intro t _
  exact (good_slice F t V β ok admissible).on_window hm

/-- Recombine every actual tag. Rooted gauge invariance is used only
to pass to this forest slice. -/
theorem forest_read_full (F : Forest S.ratio) (β : ℝ) (V : Config G c)
    (ok : S.patch.Branches S.kernel G) (D : Lit R (Config G f))
    (admissible : Leaf.All D) (invariant : GaugeInvariant D) :
    forestRead F β V D Set.univ = Actual.Push S β D V := by
  rw [forest_read_tags F β V ok D admissible _ MeasurableSet.univ,agreed V β ok admissible]
  apply sum_congr rfl
  intro t _
  rw [Set.indicator_univ,pack F t V β ok admissible invariant]

theorem forest_read_split (F : Forest S.ratio) (β : ℝ) (V : Config G c)
    (ok : S.patch.Branches S.kernel G) (D : Lit R (Config G f))
    (admissible : Leaf.All D) (invariant : GaugeInvariant D)
    (A : Set (F.Slice G)) (hm : MeasurableSet A) :
    Actual.Push S β D V = forestRead F β V D A + forestRead F β V D Aᶜ := by
  rw [agreed V β ok admissible,forest_read_tags F β V ok D admissible _ hm,
    forest_read_tags F β V ok D admissible _ hm.compl,←sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [pack F t V β ok admissible invariant,split_cost (good_slice F t V β ok admissible) hm]

/-- Precisely the native fourth error after all tag choices have been
summed. The event lives on the genuine atlas, including its seams. -/
theorem original_outside_is_mask (F : Forest S.ratio) (g:ℝ) (x:fieldDir G c 1)
    (ok : S.patch.Branches S.kernel G) (D : Lit R (Config G f)) (admissible : Leaf.All D)
    (A : Set (F.Slice G)) (hm : MeasurableSet A) :
    ∑ t:S.Choices, charge (F.order G) (Integral.outside F t g x A D) =
      forestRead F (temperature g) (sample g x) D Aᶜ :=
  (forest_read_tags F (temperature g) (sample g x) ok D admissible Aᶜ hm.compl).symm

end YM.Integration.FVA1Physical.OriginalMixedWilson
