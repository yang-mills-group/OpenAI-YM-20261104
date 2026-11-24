import YM.Integration.WilsonWindowJointPurchase

/-! Co-elect the independently booked colors on the same original run and delay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletColorMenu
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection WilsonWindowJointPurchase
variable {G : Gauge}

def colors (p : Prediction G) (offers : G.ColorIndex → Prediction G)
    (us : List G.ColorIndex) : Prediction G := fun {_} {_} {_} F =>
  us.foldr (fun a carried => carried ∧ offers a F) (p F)

theorem prices (p : Prediction G) (offers : G.ColorIndex → Prediction G)
    (paid : WilsonFundedWindowMenu.AllPrices (@p))
    (sold : ∀ a, WilsonFundedWindowMenu.AllPrices (@offers a)) (us : List G.ColorIndex) :
    WilsonFundedWindowMenu.AllPrices (@colors G (@p) (@offers) us) := by
  induction us with
  | nil => exact paid
  | cons a rest ih =>
    intro s M
    exact joint (ih s M) (sold a s M)

theorem reads (R : Run G) (p : Prediction G) (offers : G.ColorIndex → Prediction G)
    (us : List G.ColorIndex) :
    colors (@p) (@offers) us R.kit → p R.kit ∧ ∀ a ∈ us, offers a R.kit := by
  induction us with
  | nil => exact fun h => ⟨h, by simp⟩
  | cons b rest ih =>
    intro h
    obtain ⟨ambient, older⟩ := ih h.1
    refine ⟨ambient, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | earlier
    · exact h.2
    · exact older a earlier

end YM.Integration.WilsonReportingAbsoluteInletColorMenu
