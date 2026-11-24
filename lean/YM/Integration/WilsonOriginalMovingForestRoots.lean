import YM.AllOrder.Floe.Lamps
import YM.Integration.WilsonMovingMentorSchools

/-! One original degree-resolved formal root chosen on the physical before-length
prices. Each subsequent forecast receives that very root before choosing its
first size. The final claim keeps it on the actual increased sheet and alloy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMovingForestRoots

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open AllOrder.Floe.Step
variable {G : Gauge}

abbrev Continuation (G : Gauge) :=
  (profile : ℕ → Stage) → (prices : MapPrices) → (K : KernelChoices) →
    PlanV.Roots (G:=G) profile prices K → Prediction G

def Filed (clause : Continuation G) : Prediction G := fun {M} {D} {_} F =>
  ∃ r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel,
    (∀ j, r.Rise j (D.L j).val) ∧ clause M.p.profile M.K M.p.kernel r F

theorem joint (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ)
    (clause : Continuation G)
    (entered : ∀ (s : Sheet G) (T : MapPrices)
      (r : PlanV.Roots (G:=G) s.profile (ThroughLaunch.raging s T) s.kernel),
      WilsonMovingCommonPrices.Prepaid ask slow
        (@clause s.profile (ThroughLaunch.raging s T) s.kernel r) s (ThroughLaunch.raging s T)) :
    WilsonMovingCommonPrices.AllPrices ask slow (@Filed G clause) := by
  intro s cost targets E charts C v baton wanting wage
  obtain ⟨r⟩ := PlanV.acquire simple s.profile (ThroughLaunch.raging s cost) s.kernel
  obtain ⟨size,early⟩ := r.prize
  obtain ⟨u,buy⟩ := entered s cost r targets E charts C v baton wanting wage
  refine ⟨u ⊔ size,?_⟩
  intro l hl upper D w U Z φ S θ p fee V pocket cap
  obtain ⟨first,second⟩ := sup_le_iff.mp hl
  obtain ⟨Y,floor,full⟩ := buy l first upper D w U Z φ S θ p fee V pocket cap
  refine ⟨Y,floor,?_⟩
  intro delay hy K I marked B light alloy η q E' X J K' b hZ hc hm
  exact ⟨r, fun j => early j _ ((second j).trans (D.large j).need),
    full delay hy K I marked B light η q E' X J K' b hZ hc hm⟩

theorem schools (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow
      (@Filed G (fun _ _ _ _ => @WilsonMovingStoredFactor.OnMenu G
        (@WilsonMovingMentorSchools.Admitted G ask))) := by
  exact joint simple ask slow _ fun s T _ =>
    WilsonMovingMentorSchools.bought simple ask slow s T

end YM.Integration.WilsonOriginalMovingForestRoots
end
