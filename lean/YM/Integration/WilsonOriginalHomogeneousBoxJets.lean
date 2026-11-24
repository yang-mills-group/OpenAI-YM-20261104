import YM.Integration.WilsonOriginalFundedWindowJets
import YM.Integration.WilsonOriginalCompactAxisExpense

/-! Gevrey bounds for all derivatives in a real chart direction of the
elected homogeneous Wilson mean, before any choice of Fourier frequency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousBoxJets
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

    {m : ℕ} (embed : (Fin (m+1) → ℝ) →ₗ[ℝ] Points n)
    (direction : ∀ i, ‖embed (Pi.single i (1:ℝ))‖ ≤ 1) :
    ∃ B D : ℝ, 0 < B ∧ 0 ≤ D ∧ ∀ᶠ r in trail,
      ∀ (origin : Points n) (i : Fin (m+1)) (a l h : Fin (m+1) → ℝ)
        (rest : Fin m → UnitAddCircle) (x : ℝ), a i < l i → h i < a i+1 →
        x ∈ Icc (a i) (a i+1) →
        let base := origin+embed (WilsonOriginalPhysicalBoxSlices.positions i a rest x)
        (∀ j k : Fin n, j ≠ k → η ≤ dist (base j) (base k)) → ∀ k : ℕ,
        ‖iteratedDeriv k (fun t : ℝ => WilsonOriginalFourierBoxIntegral.localize a l h
          (fun q => S.classMoment S d (r • (origin+embed q))
            (fun j => homogeneous F J Z r (d j) (v j))) (i.insertNth (t:UnitAddCircle) rest)) x‖ ≤
        (u r)⁻¹^2*Real.exp (D*(u r)⁻¹^4)*((B/u r)^(2*k)*(k.factorial:ℝ)^2) := by
  obtain ⟨B,D,hB,hD,room⟩ := WilsonOriginalFundedWindowJets.original run Z d v gap clock
  refine ⟨B,D,hB,hD,?_⟩
  filter_upwards [room] with r paid
  intro origin i a l h rest x left right hx
  dsimp only
  intro sep k
  apply (WilsonOriginalCompactAxisExpense.original i a l h rest _ left right hx k).trans
  let base := origin+embed (WilsonOriginalPhysicalBoxSlices.positions i a rest x)
  have charge := paid base sep (embed (Pi.single i (1:ℝ))) (direction i) (l i) (h i) x k
  simpa only [base,map_add,map_smul,add_assoc,Pi.mul_def] using charge

end YM.Integration.WilsonOriginalHomogeneousBoxJets
