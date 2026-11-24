import YM.AllOrder.Transit.Funding
import YM.Integration.WilsonMovingMentorPhase
import YM.Integration.WilsonMovingMentorSpec

/-! The true root receives its original Tour on the selected covariance table and
the canonical phase of the same Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorTravel
open Precision RG RG.Supply Push Push.PriceCompiler PhysicalNext PhysicalNext.ThroughLaunch Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Roof
open AllOrder.Floe.Step WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor
open WilsonOriginalMovingForestRoots WilsonLimitConstruction.FundedPredictionSupply

def Ride {G : Gauge} (simple : G.Simple) : Continuation G := fun _ _ _ pre {M} {D} {A} F =>
  AtMenu F → ∀ r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel, HEq pre r →
    AllOrder.Transit.Tour F.shape r (WilsonMovingMentorSeats.appointment (M:=M) simple D r)
      F.v F.prices F.t F.span F.recordP F.scout (wind F.menu) A.delay

theorem entered {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ)
    (s : Sheet G) (cost : MapPrices) (r : PlanV.Roots (G:=G) s.profile (raging s cost) s.kernel) :
    WilsonMovingCommonPrices.Prepaid ask slow (@Ride G simple _ _ _ r) s (raging s cost) := by
  intro rows E charts C v baton wanting wage
  obtain ⟨h,goods⟩ := AllOrder.Transit.must s (raging s cost) E v
  refine ⟨h,?_⟩
  intro l hh earlier D w u Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s cost,chart G,chart_ok G⟩
  let table := WilsonMovingMentorSeats.appointment (M:=M) simple D r
  have needed : AllOrder.Transit.Needed M.p M.K E v l :=
    ⟨fun i j L hij fair => goods.hair i j L hij ((hh j).trans fair),
      fun j i hij L fair => goods.acts j i hij L ((hh j).trans fair)⟩
  obtain ⟨Y,outward,ride⟩ := AllOrder.Transit.predicts (X:=M) Z r table v C (rays s) mile p S
    (fun _ _=> SectorMeasure.Chi.canonical) simple needed (fun i j _=> charts i j)
    (fun j i _=> wanting j i) (fun _ i _=> by unfold rays; linarith [(s.profile i).price_pos]) cap V
  refine ⟨Y,outward,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides menu r' equal
  have same : r = r' := eq_of_heq equal
  subst r'
  have phase : wind X = fun _ _=>SectorMeasure.Chi.canonical := by
    funext j i
    exact menu j i
  change AllOrder.Transit.Tour (X:=M) (P:=θ) Z r table v C (rays s) mile p S (wind X) W'
  rw [phase]
  exact ride _ hW

def Road {G : Gauge} (simple : G.Simple) : Continuation G := fun b cost k r =>
  @Both G (@WilsonMovingMentorSeats.Received G simple b cost k r) (@Ride G simple b cost k r)

theorem road {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ)
    (s : Sheet G) (cost : MapPrices) (r : PlanV.Roots (G:=G) s.profile (raging s cost) s.kernel) :
    WilsonMovingCommonPrices.Prepaid ask slow (@Road G simple _ _ _ r) s (raging s cost) :=
  WilsonMovingMentorStagePair.paid (WilsonMovingMentorSeats.entered simple ask slow s cost r)
    (entered simple ask slow s cost r)

theorem reserved {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@Filed G (@Road G simple)) :=
  joint simple ask slow _ (road simple ask slow)

def Passed {G : Gauge} : Prediction G := fun {M} {D} {A} F =>
  ∃ (r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel) (Q : r.Tab D),
    AllOrder.Transit.Pass r Q A F

theorem paid {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Passed G)) := by
  have road := reserved simple ask slow
  have lodge := WilsonMovingMentorLodge.paid (G:=G) ask slow AllOrder.Shop.edgeW AllOrder.Shop.edge_pp
  have both := WilsonMovingMentorOffer.together ask slow road lodge
  intro s cost rows E charts C v baton wanting wage
  obtain ⟨q,quote⟩ := both s cost rows E charts C v baton wanting wage
  refine ⟨q,?_⟩
  intro l hl earlier D w u Z φ S θ p P V pocket cap
  obtain ⟨W,hw,cash⟩ := quote l hl earlier D w u Z φ S θ p P V pocket cap
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owned menu
  obtain ⟨⟨r,rent,atRoot⟩,ladder⟩ := cash W' hW b I hp B light η z E' X J K' f shelter works divides owned menu
  have income := atRoot.1 r HEq.rfl
  have ride := atRoot.2 menu r HEq.rfl
  exact ⟨r,_,⟨ride,WilsonMovingMentorSpec.received _ _ rent income ladder owned⟩⟩

end YM.Integration.WilsonMovingMentorTravel
end
