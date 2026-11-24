import YM.Integration.WilsonSurveyedColorQuotient
import YM.FVA2.SteadyBooked

/-! Linearity of the actual marked minimal-subtraction calculation before
any evanescent components are evaluated at physical dimension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorDimensional
open MS MS.Arts MS.Motif MS.Land MS.Local.Physical MS.Dock MS.Pearl MS.Train
open MS.Outlook FVA2.ArchTurn
open scoped BigOperators Classical
variable {G : Gauge} {B B' : Deck G} {A : Booked B} {A' : Booked B'}

def source (A : Booked B) (h : ℕ) (i : Plaid B h) :=
  MS.Emit.gloss (Literal.linear (Mob G) (A.optics h i))

/-- Combine the full continuation, the marked output and its pole ledger on
the same vacuum, at every regulator and every coupling coefficient. -/
theorem combined (M : MS_Data G A) (h : ℕ) (c : Plaid B h → ℝ) :
    comet h 0 M.bulk (∑ i, (c i:ℂ) • source A h i)
      (∑ i, (c i:ℂ) • M.marks h i) (∑ i, (c i:ℂ) • M.poles h i) :=
  comet_t Finset.univ fun i _ => comet_s (M.markOK h i) (c i)

/-- A transformed dimensional source expressed in its booked frame keeps
its complete Laurent counterterm, and its renormalized physical archive uses
the same coefficients and the same coupling. The two calculations may have
different decks and separately commissioned vacuum solutions. -/
theorem archived (M : MS_Data G A) (M' : MS_Data G A') (h : ℕ)
    (j : Plaid B' h) (c : Plaid B h → ℝ)
    (filed : source A' h j = ∑ i, (c i:ℂ) • source A h i) :
    M'.poles h j = ∑ i, (c i:ℂ) • M.poles h i ∧
    Archive h (M'.marks h j) = Archive h (∑ i, (c i:ℂ) • M.marks h i) := by
  have left := M'.markOK h j
  change comet h 0 M'.bulk (source A' h j) (M'.marks h j) (M'.poles h j) at left
  rw [filed] at left
  have right := combined M h c
  obtain ⟨polars,rows⟩ := unique_M left right (unique_B M'.bulkOK M.bulkOK).2
  exact ⟨polars,archive_h rows (fun k => (Dock.gang (left k)).dost)
    (fun k => (Dock.gang (right k)).dost)⟩

end YM.Integration.WilsonSurveyedColorDimensional
end
