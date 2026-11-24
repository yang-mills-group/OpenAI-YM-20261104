import YM.Integration.WilsonOriginalHomogeneousTube
import YM.Integration.WilsonOriginalPhysicalDiscCurrency

/-! The separated compact mean on the published homogeneous appointment
has its spectral width and exponential bound at the actual measured heater. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousMeteredDisc
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)


include run in
theorem original {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {η : ℝ} (gap : 0 < η) {meter : ℝ → ℝ} (clock : Coupling G meter) :
    ∃ (ρ D : ℝ), 0 < ρ ∧ 0 ≤ D ∧ ∀ᶠ r in trail, ρ*(meter r)^2 ≤ ρ ∧
      ∀ x : Points n, (∀ i j : Fin n, i ≠ j → η ≤ dist (x i) (x j)) →
      ∀ a : Points n, ‖a‖ ≤ 1 → ∃ g : ℂ → ℂ, DiffContOnCl ℂ g (ball 0 ρ) ∧
        (∀ z ∈ sphere 0 ρ, ‖g z‖ ≤ Real.exp (D*(meter r)⁻¹^4)) ∧
        ((fun t : ℝ => S.classMoment S d (r • (x+t • a))
           (fun i => homogeneous F J Z r (d i) (v i))) =ᶠ[𝓝 0] fun t : ℝ => g t) := by
  obtain ⟨ρ,A,p,hρ,hA,bill⟩ := WilsonOriginalHomogeneousTube.original run Z d v gap
  obtain ⟨D,hD,expense⟩ := WilsonOriginalPhysicalDiscCurrency.original clock A hA p
  have cold := WilsonOriginalTemperatureDecay.original clock
  refine ⟨ρ,D,hρ,hD,?_⟩
  filter_upwards [bill,expense,clock.positive,(tendsto_order.mp cold).2 1 zero_lt_one]
    with r tube cost positive below
  refine ⟨mul_le_of_le_one_right hρ.le (pow_le_one₀ positive.le below.le),?_⟩
  intro x sep a ha
  obtain ⟨g,cont,price,real⟩ := tube x sep a ha
  have diff := cont.differentiableOn
  exact ⟨g,⟨diff.mono ball_subset_closedBall,diff.continuousOn.mono closure_ball_subset_closedBall⟩,
    fun z hz => (price z (sphere_subset_closedBall hz)).trans cost, real⟩
end YM.Integration.WilsonOriginalHomogeneousMeteredDisc
