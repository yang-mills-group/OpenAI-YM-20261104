import YM.Integration.WilsonOriginalFiledMeanJets
import YM.Integration.WilsonOriginalFiledBoxWindow

/-! Gevrey bounds for all derivatives in a real chart direction of the
elected homogeneous Wilson mean, before any choice of Fourier frequency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFundedWindowJets
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
    {η : ℝ} (gap : 0 < η) {u : ℝ → ℝ} (clock : Coupling G u)
    : ∃ B D : ℝ, 0 < B ∧ 0 ≤ D ∧ ∀ᶠ r in trail, ∀ x : Points n,
      (∀ i j : Fin n, i ≠ j → η ≤ dist (x i) (x j)) → ∀ a : Points n, ‖a‖ ≤ 1 →
      ∀ lo hi y : ℝ, ∀ k : ℕ,
        ‖iteratedDeriv k ((fun t : ℝ => WilsonOriginalGevreyWindow.window lo hi (y+t))*
          (fun t : ℝ => S.classMoment S d (r • (x+t • a))
            (fun i => homogeneous F J Z r (d i) (v i)))) 0‖ ≤
        (u r)⁻¹^2*Real.exp (D*(u r)⁻¹^4)*((B/u r)^(2*k)*(k.factorial:ℝ)^2) := by
  obtain ⟨B,D,hB,hD,room⟩ := WilsonOriginalFiledMeanJets.original run Z d v gap clock 1 32 (by norm_num) (by norm_num)
  refine ⟨B,D,hB,hD,?_⟩
  filter_upwards [room] with r hr
  intro x sep a ha lo hi y k
  have sc : ContDiffAt ℝ k (fun t : ℝ => WilsonOriginalGevreyWindow.window lo hi (y+t)) 0 :=
    ((WilsonOriginalFiledBoxWindow.smooth lo hi).comp (contDiff_const.add contDiff_id)).contDiffAt
  have paid (j : ℕ) (_ : j ≤ k) :
      ‖iteratedDeriv j (fun t : ℝ => WilsonOriginalGevreyWindow.window lo hi (y+t)) 0‖ ≤
      1*(32:ℝ)^j*(j.factorial:ℝ)^2 := by
    rw [iteratedDeriv_comp_const_add]
    simpa using WilsonOriginalGevreyWindow.original lo hi y j
  simpa only [one_mul] using hr x sep a ha _ k sc paid

end YM.Integration.WilsonOriginalFundedWindowJets
