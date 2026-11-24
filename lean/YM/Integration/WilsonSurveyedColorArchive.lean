import YM.Integration.WilsonSurveyedColorSubtraction

/-! A common prescription on the two dimensional Laurent ledgers suffices
for every ordered, separated ordinary MS correlation. Both books supply
their own finite parts and absolute integration prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorArchive
open Function MS MS.Arts MS.Local.Physical MS.Pearl MS.Dock MS.Emit MS.Outlook
open MS.Land MS.Rake MS.Rake.Geo MS.Theater MS.Tide
open WilsonSurveyedColorHearing WilsonSurveyedColorSubtraction
open Function Set Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone City Latch Latch.Job Rake Arts Osc Snap
open Land Local.Physical Rake.Geo Tide Vane
open WilsonSurveyedColorQuotient WilsonSurveyedColorFlow WilsonSurveyedColorHearing
open WilsonSurveyedColorContinuum
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {I W : Type}

theorem site {h h' : ℕ} (level : h=h') (P : Geo I) (F F' : ℕ → Flats G)
    (left : ∀ k, Stay h (F k)) (right : ∀ k, Stay h' (F' k))
    (same : ∀ k, ledger U (F k)=F' k) (k : ℕ) :
    filed U (circle P.η (Archive h F) k) = circle P.η (Archive h' F') k := by
  subst h'
  funext i t
  exact congrFun (finitePart U (same k) (left k) (right k) t (P.η i)) 0

variable {B B' : Deck G} {O : Booked B} {O' : Booked B'} [LinearOrder W]
theorem labelled [Fintype W] {M : MS_Data G O} {M' : MS_Data G O'}
    {u : W → Rake.Label B} {u' : W → Rake.Label B'} {x : W → QP}
    (sep : Injective x) (ν : ℝ) (level : ∀ w, (u w).h=(u' w).h)
    (vacuum : ∀ k, ledger U (M.bulk k)=M'.bulk k)
    (names : ∀ w k, ledger U (M.marks (u w).h (u w).item k) =
      M'.marks (u' w).h (u' w).item k) :
    Dial.tour M u ν x = Dial.tour M' u' ν x := by
  apply WilsonSurveyedColorBank.labelled U sep ν
  · exact site U rfl _ _ _ (fun k => (gang (M.bulkOK k)).dost)
      (fun k => (gang (M'.bulkOK k)).dost) vacuum
  · intro w
    exact site U (level w) _ _ _ (fun k => (gang (M.markOK _ _ k)).dost)
      (fun k => (gang (M'.markOK _ _ k)).dost) (names w)

end YM.Integration.WilsonSurveyedColorArchive
end
