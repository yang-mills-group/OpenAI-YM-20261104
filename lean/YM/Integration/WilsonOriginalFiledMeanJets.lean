import YM.Integration.WilsonOriginalHomogeneousMeteredDisc
import YM.Integration.WilsonOriginalPhysicalTubeExpense

/-! Gevrey bounds for all derivatives in a real chart direction of the
elected homogeneous Wilson mean, before any choice of Fourier frequency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledMeanJets
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
    {η : ℝ} (gap : 0 < η) {u : ℝ → ℝ} (clock : Coupling G u) (C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ B D : ℝ, 0 < B ∧ 0 ≤ D ∧ ∀ᶠ r in trail, ∀ x : Points n,
      (∀ i j : Fin n, i ≠ j → η ≤ dist (x i) (x j)) → ∀ a : Points n, ‖a‖ ≤ 1 →
      ∀ χ : ℝ → ℂ, ∀ k : ℕ, ContDiffAt ℝ k χ 0 →
        (∀ j ≤ k, ‖iteratedDeriv j χ 0‖ ≤ C*H^j*(j.factorial:ℝ)^2) →
        ‖iteratedDeriv k (χ*(fun t : ℝ => S.classMoment S d (r • (x+t • a))
          (fun i => homogeneous F J Z r (d i) (v i)))) 0‖ ≤
          C*(u r)⁻¹^2*Real.exp (D*(u r)⁻¹^4)*((B/u r)^(2*k)*(k.factorial:ℝ)^2) := by
  obtain ⟨ρ,D,hρ,hD,tube⟩ := WilsonOriginalHomogeneousMeteredDisc.original run Z d v gap clock
  have base : 0 < WilsonOriginalPhysicalTubeExpense.B H ρ :=
    Real.sqrt_pos.2 (mul_pos zero_lt_two ((inv_pos.mpr hρ).trans_le (le_max_right _ _)))
  refine ⟨_,D,base,hD,?_⟩
  have cold := WilsonOriginalTemperatureDecay.original clock
  filter_upwards [tube,clock.positive,(tendsto_order.mp cold).2 1 zero_lt_one] with r paid pos small
  intro x s a ha χ k sc offer
  obtain ⟨g,disc,bound,onAxis⟩ := paid.2 x s a ha
  have an : AnalyticAt ℂ g 0 := disc.differentiableOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have smooth : ContDiffAt ℝ k (fun t : ℝ => g t) 0 := by
    have h : ContDiffAt ℂ k g (↑(0:ℝ):ℂ) := by simpa using (an.contDiffAt : ContDiffAt ℂ k g 0)
    exact (h.restrict_scalars ℝ).comp 0 Complex.ofRealCLM.contDiff.contDiffAt
  apply (WilsonOriginalPhysicalTubeExpense.original 0 (u r) ρ ρ D C H pos small.le hρ paid.1 hC hH k onAxis
    (by simpa using disc) (by simpa using bound) sc (smooth.congr_of_eventuallyEq onAxis) offer).2

end YM.Integration.WilsonOriginalFiledMeanJets
