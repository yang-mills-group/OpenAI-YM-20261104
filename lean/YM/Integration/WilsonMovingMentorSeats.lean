import YM.AllOrder.Floe.Campus
import YM.Integration.WilsonOriginalMovingForestRoots
import YM.Integration.WilsonMovingMentorStagePair

/-! The same root chosen before the block lengths issues the native covariance table
and the full original temperature receipt on the eventual physical factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorSeats
open Precision RG RG.Supply Push Push.PriceCompiler PhysicalNext PhysicalNext.ThroughLaunch Org Next.Foundations
open AllOrder.Floe.Step WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMovingForestRoots

/-- The original income table is nominated after the lengths are known and before
either the Tour or the teaching offices ask for a delay. -/
def appointment {G : Gauge} {M : Metals G} (simple : G.Simple) (D : Rolls M.p)
    (r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel) : r.Tab D :=
  Classical.choice (PlanV.Roots.options (X:=M) D r simple)

/-- The early root and the root of the issued factor carry the same table. -/
def Received {G : Gauge} (simple : G.Simple) : Continuation G := fun _ _ _ pre {M} {D} {A} _ =>
  ∀ r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel, HEq pre r →
    PlanV.Roots.Receives D r (appointment (M:=M) simple D r) A.delay

theorem entered {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ)
    (s : Sheet G) (cost : MapPrices) (r : PlanV.Roots (G:=G) s.profile (raging s cost) s.kernel) :
    WilsonMovingCommonPrices.Prepaid ask slow (@Received G simple _ _ _ r) s (raging s cost) := by
  intro rows E charts C v baton wanting wage
  obtain ⟨q, affordable⟩ := r.prize
  refine ⟨q,?_⟩
  intro l hl earlier D w u Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s cost,chart G,chart_ok G⟩
  have rate (j : ℕ) : r.Rise j (D.L j).val :=
    affordable j _ ((hl j).trans (D.large j).need)
  let table := appointment (M:=M) simple D r
  obtain ⟨W, hw, doors⟩ := PlanV.Roots.summit (X:=M) D r rate table V
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides r' equal
  have same : r = r' := eq_of_heq equal
  subst r'
  exact doors _ hW

theorem paid {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@Filed G (@Received G simple)) :=
  joint simple ask slow _ (entered simple ask slow)

end YM.Integration.WilsonMovingMentorSeats
end
