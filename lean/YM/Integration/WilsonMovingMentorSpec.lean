import YM.AllOrder.Floe.Relay
import YM.Integration.WilsonMovingMentorSeats
import YM.Integration.WilsonMovingMentorLodge

/-! The five clauses of the original PlanV specification are purchased for one
field, covariance, factor, and hierarchy before any reporting period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorSpec
open PhysicalNext PhysicalNext.Repeat AllOrder.Floe.Step
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

def Filed {G : Gauge} : Prediction G := fun {M} {D} {A} F =>
  ∃ (r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel) (Q : r.Tab D),
    PlanV.Spec r Q A F

theorem received {G : Gauge} {M : Org.Metals G} {D : RG.Supply.Rolls M.p} {A : Org.Alloy M D}
    (F : Roost.Factor A) {r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel} (Q : r.Tab D)
    (rent : ∀ j, r.Rise j (D.L j).val) (income : PlanV.Roots.Receives D r Q A.delay)
    (ladder : WilsonMovingMentorLodge.Held AllOrder.Shop.edgeW F)
    (base : WilsonMovingMentorOwnership.Owned F) : PlanV.Spec r Q A F :=
  ⟨rent,income,ladder,base.1,base.2⟩

theorem paid {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Filed G)) := by
  have seats := WilsonMovingMentorSeats.paid simple ask slow
  have lodge := WilsonMovingMentorLodge.paid (G:=G) ask slow AllOrder.Shop.edgeW AllOrder.Shop.edge_pp
  have both := WilsonMovingMentorOffer.together ask slow seats lodge
  intro s cost rows E charts C v baton wanting wage
  obtain ⟨q,quote⟩ := both s cost rows E charts C v baton wanting wage
  refine ⟨q,?_⟩
  intro l hl earlier D w u Z φ S θ p P V pocket cap
  obtain ⟨W,hw,cash⟩ := quote l hl earlier D w u Z φ S θ p P V pocket cap
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owned menu
  obtain ⟨⟨r, rent, same⟩, ladder⟩ := cash W' hW b I hp B light η z E' X J K' f shelter works divides owned menu
  have bear := same r HEq.rfl
  exact ⟨r,_,received _ _ rent bear ladder owned⟩

end YM.Integration.WilsonMovingMentorSpec
end
