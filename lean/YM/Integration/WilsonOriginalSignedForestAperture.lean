import YM.Integration.ManuscriptQLocalActualLog
import YM.WilsonCoeffUV.VacuumLaw
import YM.Comparison.RG02.Laplace.Choice

/-! The complete original marked density on a transported compact aperture,
before its normalized connected logarithm. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalSignedForestAperture
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Push.SectorMeasure WilsonCoeffUV WilsonCoeffUV.Fk
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}

def column (F : Forest S.ratio) (t : S.Choices) (A : Set (F.Slice G))
    (β : ℝ) (V : Config G c) (Z : Lit Γ (Config G f)) : Poly Γ :=
  charge (F.order G) (A.indicator (stack t V β Z ∘ F.drape))

omit [Fintype ι] in
theorem change (F H : Forest S.ratio) (t : S.Choices) (A : Set (F.Slice G))
    (β : ℝ) (V : Config G c) (Z : Lit Γ (Config G f)) (invariant : GaugeInvariant Z)
    (branches : S.patch.Branches S.kernel G) :
    column F t A β V Z = column H t (Profiles.reroute F H G '' A) β V Z := by
  let ζ := Profiles.reroute F H G
  let Y := stack t V β Z
  have he : A.indicator (Y ∘ F.drape) = ((ζ '' A).indicator (Y ∘ H.drape)) ∘ ζ := by
    funext a
    by_cases h : a∈A
    · rw [Function.comp_apply,Set.indicator_of_mem (Set.mem_image_of_mem _ h),Set.indicator_of_mem h]
      change Y (F.drape a) = Y (H.drape (Profiles.wick H (F.drape a)))
      rw [Profiles.wears]
      exact (stack_rooted t V β branches _ (H.fold_root _) invariant _).symm
    · have nh : ζ a∉ζ '' A := by
        rintro ⟨b,hb,e⟩
        exact h (ζ.injective e ▸ hb)
      simp [Function.comp_apply,h,nh]
  unfold column
  change charge (F.order G) (A.indicator (Y ∘ F.drape)) = _
  rw [he]
  ext i
  exact (Profiles.spending F H G).integral_comp ζ.measurableEmbedding
    (atMark i ((ζ '' A).indicator (Y ∘ H.drape)))

variable (R : Run G) {J : Request ι} {U : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) (H : AnalyticInput J U d) (x : TestSpace J.tests)

set_option quotPrecheck false in
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
set_option quotPrecheck false in
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
set_option quotPrecheck false in
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
set_option quotPrecheck false in
local notation "Z" => ManuscriptQLocalActualLog.source R d H x

def reading (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (V : Config G (R.family.side d.level d.period)) :=
  ∑ t : (Δ).Choices,column F t (A t) (P₁).beta V (Z)

theorem original (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (V : Config G (R.family.side d.level d.period)) :
    let H₀ := repeatF (Δ)
    let A' := fun t => Profiles.reroute F H₀ G '' A t
    let seen := reading R d H x F A V
    let filed := reading R d H x H₀ A' V
    seen = filed ∧ Extra.Trajectories.connected (((P₀).eval V)⁻¹ • seen) =
      Extra.Trajectories.connected (((P₀).eval V)⁻¹ • filed) := by
  intro H₀ A' seen filed
  have eq : seen=filed := by
    apply Finset.sum_congr rfl
    intro t _
    exact change F H₀ t (A t) (P₁).beta V (Z) (ManuscriptQLocalActualLog.floor R d H x).gauges
      (R.family.path.levels.blocks d.level d.period).branches
  exact ⟨eq,congrArg (fun a => Extra.Trajectories.connected (((P₀).eval V)⁻¹ • a)) eq⟩

theorem complete (F : Forest (Δ).ratio) (V : Config G (R.family.side d.level d.period)) :
    reading R d H x F (fun _ => Set.univ) V = Actual.Push (Δ) (P₁).beta (Z) V := by
  have floor := ManuscriptQLocalActualLog.floor R d H x
  have b := (R.family.path.levels.blocks d.level d.period).branches
  rw [Actual.agreed V (P₁).beta b floor.safe]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [column,Set.indicator_univ] using (Actual.pack F t V (P₁).beta b floor.safe floor.gauges).symm

end YM.Integration.WilsonOriginalSignedForestAperture
