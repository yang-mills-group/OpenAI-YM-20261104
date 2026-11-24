import YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
import YM.Integration.WilsonMacroscopicRichMSCoefficient

/-! The public separated packet and its independently issued finite MS coefficient
are heard on one normalized exterior bank in the full physical output space. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourQuotient
open Function Filter Finset Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace FVA2 FVA2.Register FVA2.O FVA2.ColorCode FVA2.Scale
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesNormalizedPivot
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
local notation "B₀" => Press.portDeck G

def packet (P : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {n : ℕ} (h : ℕ) (d : Fin n → ℕ) (v : (i : Fin n) → (Bel R.family.book).Field (d i))
    (r : ℝ) (x : Points n) : S.Field h :=
  P.packet h (RG17.posed r x) (fun i => homogeneous F J Z r (d i) (v i)) 0

def atom (h : ℕ) (a : Glyph B₀ h) : (Bel R.family.book).Field h :=
  (exactField R.family.labels h).symm ((Daylight B₀ h) a)

theorem row {n h : ℕ} (D : Contacts.Foci (Bel R.family.book) h)
    (M : MS_Data G (Position.OpenAxis.Plot B₀)) (d : Fin n → ℕ)
    (v : (i : Fin n) → (Bel R.family.book).Field (d i)) (μ : ℝ) (x : Points n)
    (r t : ℝ) (q : ℕ) (y : S.Field h) (j : D.index) :
    readout F J Z D r
      (y - homogeneous F J Z r h (WilsonMacroscopicRichMSCoefficient.field R M h d v μ x t q)) j =
      probe F J Z (D.shell j) r h y -
        ∑ a : Glyph B₀ h, WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x t q a *
          probe F J Z (D.shell j) r h (homogeneous F J Z r h (atom (R := R) h a)) := by
  change probe F J Z (D.shell j) r h (_-_) = _
  simp only [WilsonMacroscopicRichMSCoefficient.field, atom, map_sub, map_sum, map_smul, smul_eq_mul]

theorem original {Y : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d) (simple : G.Simple)
    (h : ℕ) :
    ∃ D : Contacts.Foci (Bel R.family.book) h, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ r in trail, ∀ (P : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
        (M : MS_Data G (Position.OpenAxis.Plot B₀)) (n : ℕ) (d : Fin n → ℕ)
        (v : (i : Fin n) → (Bel R.family.book).Field (d i)) (μ : ℝ) (x : Points n)
        (t : ℝ) (q : ℕ),
        let y := packet F J Z P h d v r x
        let c := WilsonMacroscopicRichMSCoefficient.coefficient R M d v μ x t q (h := h)
        ‖(homogeneous F J Z r h).symm y - WilsonMacroscopicRichMSCoefficient.field R M h d v μ x t q‖ ≤
         K * ‖fun j : D.index => probe F J Z (D.shell j) r h y -
          ∑ a : Glyph B₀ h, c a * probe F J Z (D.shell j) r h
            (homogeneous F J Z r h (atom (R := R) h a))‖ := by
  obtain ⟨D,K,hK,bank⟩ := WilsonMatrixTicketLanesNormalizedPivot.original F J Z lead paid simple h
  refine ⟨D,K,hK,?_⟩
  filter_upwards [bank] with r measured
  intro P M n d v μ x t q
  dsimp only
  let y := packet F J Z P h d v r x
  let a := WilsonMacroscopicRichMSCoefficient.field R M h d v μ x t q
  have actual := measured (y - homogeneous F J Z r h a)
  rw [map_sub, LinearEquiv.symm_apply_apply] at actual
  have eq := funext (row F J Z D M d v μ x r t q y)
  rw [eq] at actual
  exact actual

end YM.Integration.WilsonThermometerUnitFilingFourQuotient
