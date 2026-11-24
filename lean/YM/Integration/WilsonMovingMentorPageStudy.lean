import YM.Integration.WilsonMovingMentorPageTuition
import YM.Integration.WilsonMovingMentorTravel

/-! The field, covariance table, teaching offices and registered salary
forecast all belong to the same stored physical factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorPageStudy
open Precision RG RG.Supply Push Push.PriceCompiler PhysicalNext PhysicalNext.ThroughLaunch Org
open PhysicalNext.Repeat AllOrder.Floe.Step QuadraticLocal WilsonOriginalMovingForestRoots
open WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedPredictionSupply WilsonMovingStoredFactor

def Panel {G : Gauge} (simple : G.Simple) (ψ : ℕ → ℕ) : Continuation G := fun b cost k r =>
  @Both G (@WilsonMovingMentorTravel.Road G simple b cost k r) (@WilsonMovingMentorPageTuition.Taught G simple ψ b cost k r)

def Enrolled {G : Gauge} (ψ : ℕ → ℕ) : Prediction G := fun {M} {D} {A} F =>
  ∃ (r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel) (Q : r.Tab D)
    (books : Mentor.Offices.Books r D Q ψ) (Qa : Mentor.Forecast r D Q ψ books),
      AllOrder.Transit.Pass r Q A F ∧ Mentor.Offices.Sales r D Q F.shape F.scout ψ books ∧
        Mentor.Educated r D Q F.shape F.scout ψ books A.delay ∧ (∀ j, Poetry.Agenda.Crews r ψ j (D.L j).val) ∧
        (∀ j, MintClock.Employment r ψ j (D.L j)) ∧
        MintClock.Hospital r D Q F.target ψ books Qa A.delay ∧ MintClock.Regency r D Q F.target ψ books Qa A.delay ∧ Spill.Raffle.Warm G r A.delay ψ ∧
        WilsonMovingMentorRootRadius.Income (M:=M) r ψ A.delay

theorem paid {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) (ψ : ℕ → ℕ) (shorter : MintClock.splits ≤ ψ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Enrolled G ψ)) := by
  have rooted : WilsonMovingCommonPrices.AllPrices ask slow (@Filed G (@Panel G simple ψ)) :=
    joint simple ask slow _ fun s cost r => WilsonMovingMentorStagePair.paid
      (WilsonMovingMentorTravel.road simple ask slow s cost r) (WilsonMovingMentorPageTuition.entered simple ask slow ψ shorter s cost r)
  have lodge := WilsonMovingMentorLodge.paid (G:=G) ask slow AllOrder.Shop.edgeW AllOrder.Shop.edge_pp
  have both := WilsonMovingMentorOffer.together ask slow rooted lodge
  intro s cost rows E charts C v baton wanting wage
  obtain ⟨q,quote⟩ := both s cost rows E charts C v baton wanting wage
  refine ⟨q,?_⟩
  intro l hl earlier D w u Z φ S θ p P V pocket cap
  obtain ⟨W,hw,cash⟩ := quote l hl earlier D w u Z φ S θ p P V pocket cap
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owned menu
  obtain ⟨⟨r,rent,courses⟩,ladder⟩ := cash W' hW b I hp B light η z E' X J K' f shelter works divides owned menu
  have income := courses.1.1 r HEq.rfl
  have ride := courses.1.2 menu r HEq.rfl
  obtain ⟨books,Qa,sales,education,crews,hire,hospital,regency,insured,radius⟩ := courses.2 r HEq.rfl
  exact ⟨r,_,books,Qa,⟨ride,WilsonMovingMentorSpec.received _ _ rent income ladder owned⟩,sales,education,crews,hire,hospital,regency,insured,radius⟩

end YM.Integration.WilsonMovingMentorPageStudy
end
