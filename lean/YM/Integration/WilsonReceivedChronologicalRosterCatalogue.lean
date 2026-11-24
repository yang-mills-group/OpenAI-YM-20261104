import YM.Integration.WilsonReceivedChronologicalFixedRoseGridArchive

/-! A supported finite physical roster archives its nominated material before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCatalogue
open Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkStencilProgramme (Basis)
open WilsonMovingForkStencilCatalogue (Catalogue)
open WilsonMovingForkDepositedPrint (Sheet)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonReceivedChronologicalFixedRoseGridArchive (Ledger catalogue)
open Analysis Table Spec Extraction Next.UVStress StressFlux.Matching
open Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical

variable {G : Gauge} {n K f first : ℕ} (R : Run G) (d : Fin n → ℕ)
  (φ : Test n) (r : ℝ) (fine : f ≤ K)

abbrev Ages (first K : ℕ) := ↥(Ico first (K-1))

private theorem before (a : Ages first K) : a.val + 1 < K := by
  have h := mem_Ico.mp a.property
  omega

variable (room : (N per : ℕ) → K ≤ N → Prop)
  (issued : ∀ {N per : ℕ} {valid : K ≤ N}, room N per valid → (y : cells R φ r (f,per)) →
    Basis R d → (a : Ages first K) →
    Sheet R N (a.val + 1) (parent R (before a).le per (placed R fine y.val)))

def ledger : Ledger R d φ r fine := fun N per y q i _ =>
  match i with
  | 0 => none
  | a + 1 =>
    if valid : K ≤ N then
      if openAt : room N per valid then
        if active : a ∈ Ico first (K-1) then some (issued openAt y q ⟨a,active⟩) else none
      else none
    else none

def Posted (book : Catalogue R d K) {N per : ℕ} {valid : K ≤ N} (admit : room N per valid) : Prop :=
  ∀ (y : cells R φ r (f,per)) (q : Basis R d) (a : Ages first K),
    book N per (placed R fine y.val) q (a.val + 1) (before a) = some (issued admit y q a)

theorem stored :
    ∃ book : Catalogue R d K, ∀ (N per : ℕ) (valid : K ≤ N) (admit : room N per valid),
      Posted R d φ r fine room issued book admit := by
  refine ⟨catalogue R d φ r fine (ledger R d φ r fine room issued), ?_⟩
  intro N per valid admit y q a
  rw [WilsonReceivedChronologicalFixedRoseGridArchive.seated]
  simp only [ledger, dif_pos valid, dif_pos admit, dif_pos a.property]

theorem original (available : ∀ᶠ per : ℕ in atTop, ∀ (N : ℕ) (valid : K ≤ N), room N per valid) :
    ∃ book : Catalogue R d K, ∀ᶠ per : ℕ in atTop, ∀ (N : ℕ) (valid : K ≤ N),
      ∃ admit : room N per valid, Posted R d φ r fine room issued book admit := by
  obtain ⟨book, entered⟩ := stored R d φ r fine room issued
  refine ⟨book, ?_⟩
  filter_upwards [available] with per selected
  exact fun N valid => ⟨selected N valid, entered N per valid _⟩

end YM.Integration.WilsonReceivedChronologicalRosterCatalogue
end
