import YM.Integration.WilsonOriginalFiledMeanJets

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousRealGerm
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators ContDiff
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
    ∀ᶠ r in trail, ∀ x : Points n, (∀ i j : Fin n, i ≠ j → η ≤ dist (x i) (x j)) →
      ∀ a : Points n, ‖a‖ ≤ 1 → ContDiffAt ℝ ∞ (fun t : ℝ => S.classMoment S d
        (r • (x+t • a)) (fun i => homogeneous F J Z r (d i) (v i))) 0 := by
  obtain ⟨ρ,D,hρ,_,room⟩ := WilsonOriginalHomogeneousMeteredDisc.original run Z d v gap clock
  filter_upwards [room] with r paid
  intro x sep a ha
  obtain ⟨g,disc,_,onAxis⟩ := paid.2 x sep a ha
  have an : AnalyticAt ℂ g 0 := disc.differentiableOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have smooth : ContDiffAt ℝ ∞ (fun t : ℝ => g t) 0 := by
    have h : ContDiffAt ℂ ∞ g (↑(0:ℝ):ℂ) := by simpa using (an.contDiffAt : ContDiffAt ℂ ∞ g 0)
    exact (h.restrict_scalars ℝ).comp 0 Complex.ofRealCLM.contDiff.contDiffAt
  exact smooth.congr_of_eventuallyEq onAxis

theorem derivative (f : ℝ → ℂ) (x : ℝ) (h : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    DifferentiableAt ℝ (iteratedDeriv k f) x := by
  have all (j : ℕ) : ContDiffAt ℝ ∞ (iteratedDeriv j f) x := by
    induction j with
    | zero => simpa using h
    | succ j ih => rw [iteratedDeriv_succ]; exact ih.derivWithin (by simp)
  exact (all k).differentiableAt (by simp)

end YM.Integration.WilsonOriginalHomogeneousRealGerm
