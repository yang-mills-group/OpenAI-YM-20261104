import YM.Integration.WilsonMatrixTicketLanesTwoSites
import YM.Integration.WilsonMatrixTicketLanesSmearedPivot

/-! Two marked sites suffice for the fixed smooth calibrated determining profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesSmearedPair
open Function Set Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedPivot
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {Y : (Bel R.family.book).Hierarchy} (lead : PhysMS.Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d) (simple : G.Simple)

include lead paid simple

/-- A single centered insertion and a single exterior field in the same horizon,
with the original smooth reporting profiles, detect every calibrated field. -/
theorem fixed (d : ℕ) : ∃ B : Profiles R d,
    (∀ j : B.probes.index, ∃ w : (standard R.family.book.grid).Ref d,
      B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid d w) ∧ ∃ K : ℝ, 0 < K ∧
    ∀ᶠ r in trail, ∀ y : S.Field d, ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖row F J Z B r y‖ := by
  obtain ⟨D,two⟩ := WilsonMatrixTicketLanesTwoSites.fixed R.family.book.grid d
  obtain ⟨B,chosen,K,hK,he⟩ := submitted F J Z lead paid simple d D
  refine ⟨B,?_,K,hK,he⟩
  rw [chosen]
  exact two

theorem original (d : ℕ) : ∃ B : Profiles R d,
    (∀ j : B.probes.index, (B.probes.shell j).n = 1) ∧ ∃ K : ℝ, 0 < K ∧
    ∀ᶠ r in trail, ∀ y : S.Field d, ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖row F J Z B r y‖ := by
  obtain ⟨B,hB,K,hK,he⟩ := fixed F J Z lead paid simple d
  refine ⟨B,fun j => ?_,K,hK,he⟩
  obtain ⟨w,hw⟩ := hB j
  rw [hw]
  rfl

end YM.Integration.WilsonMatrixTicketLanesSmearedPair
