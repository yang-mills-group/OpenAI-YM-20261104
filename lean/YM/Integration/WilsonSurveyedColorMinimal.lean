import YM.Integration.WilsonSurveyedColorArchive
import YM.Integration.WilsonSurveyedColorDimensional

/-! Dimensional minimal-subtraction uniqueness compares pole ledgers and
punctured germs. This is enough to compare the finite named physical tour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorMinimal
open Filter Function MS MS.Arts MS.Tone MS.Local.Physical MS.Pearl MS.Train
open MS.Dock MS.Emit MS.Outlook MS.Land MS.Rake MS.Rake.Geo MS.Theater MS.Tide
open WilsonSurveyedColorHearing WilsonSurveyedColorSubtraction
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {I W : Type}

theorem finiteGerm {h : ℕ} {F F' : Flats G} (sent : Pact (ledger U F) F')
    (left : Stay h F) (right : Stay h F') (y t : ℝ) :
    allDims U (hereZ h F y t) = hereZ h F' y t := by
  apply (limit U (live0 (s:=y) (y:=t) left).wind).unique
  apply (live0 (s:=y) (y:=t) right).wind.congr
  exact (prom sent h y t).symm.trans (Eventually.of_forall fun z =>
    (congrFun (parade U h F t y) z).symm)

private theorem site {h h' : ℕ} (level : h=h') (P : Geo I) (F F' : ℕ → Flats G)
    (left : ∀ k, Stay h (F k)) (right : ∀ k, Stay h' (F' k))
    (same : ∀ k, Pact (ledger U (F k)) (F' k)) (k : ℕ) :
    filed U (circle P.η (Archive h F) k) = circle P.η (Archive h' F') k := by
  subst h'
  funext i t
  exact congrFun (finiteGerm U (same k) (left k) (right k) t (P.η i)) 0

variable {B B' : Deck G} {O : Booked B} {O' : Booked B'} [LinearOrder W]
theorem prescribed {M : MS_Data G O} {M' : MS_Data G O'}
    {u : W → Rake.Label B} {u' : W → Rake.Label B'} {x : W → QP}
    (sep : Injective x) (ν : ℝ) (level : ∀ w, (u w).h=(u' w).h)
    {p : CostsM G} {q : W → CostsM G}
    (vacuum : leader G (fun k => ledger U (M.bulk k)) (gloss (Motif.pulseX G)) p)
    (names : ∀ w, comet (u' w).h 0 (fun k => ledger U (M.bulk k))
      (WilsonSurveyedColorDimensional.source O' (u' w).h (u' w).item)
      (fun k => ledger U (M.marks (u w).h (u w).item k)) (q w)) :
    p=M'.poleS ∧ (∀ w, q w=M'.poles (u' w).h (u' w).item) ∧
      Dial.tour M u ν x = Dial.tour M' u' ν x := by
  obtain ⟨pole,bulk⟩ := unique_B vacuum M'.bulkOK
  have each w := unique_M (names w) (M'.markOK _ _) bulk
  refine ⟨pole,fun w => (each w).1,WilsonSurveyedColorBank.labelled U sep ν ?_ ?_⟩
  · exact site U rfl _ _ _ (fun k => (gang (M.bulkOK k)).dost)
      (fun k => (gang (M'.bulkOK k)).dost) bulk
  · intro w
    exact site U (level w) _ _ _ (fun k => (gang (M.markOK _ _ k)).dost)
      (fun k => (gang (M'.markOK _ _ k)).dost) (each w).2

end YM.Integration.WilsonSurveyedColorMinimal
end
