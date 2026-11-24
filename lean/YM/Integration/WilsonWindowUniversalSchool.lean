import YM.Integration.WilsonWindowCourseLaws
import YM.Integration.WilsonWindowMarkedChamber
import YM.Integration.FVA1Physical.Wilson.VariableCP5House

/-! Use the actual funded rods, books and vacuum lock to open the original
marked school. No list of marked fields is an argument to the selection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowUniversalSchool

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open ThroughLaunch Roost AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonWindowRootPurchase WilsonWindowBookPurchase

universe u
variable {G : Gauge} {φ : ℕ → ℕ}

def stages (s : Sheet G) : Orders :=
  ⟨s.first,fun i => (s.profile i).order,fun i => (s.profile i).power,
    fun i => (s.profile i).supportExponent⟩

theorem on_stages (s : Sheet G) : WithStage s (stages s) :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

def flow (C : VowsR.LawScroll G φ) : VowsR.LawScroll G φ :=
  MintClock.both G φ C (MintClock.both G φ (Spill.Walking.short G φ)
    (MintClock.both G φ (MintClock.both G φ (MintClock.Pavilion.scroll (ψ := φ) G)
      (MintClock.Pavilion.Quantity.renter (ψ := φ) G)) (Rebirth.Scholar.cycles (ψ := φ) G)))

/-- Reopen the manuscript's original house on a prescribed run. Its stage
record and penalty are the values of that run. -/
theorem house (hG : G.Simple) (R : Run G)
    (D : AllOrder.Floe.Step.PlanV.Roots (G := G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q : D.Tab R.rolls) (C : VowsR.LawScroll G φ) (B : Offices.Books D R.rolls Q φ)
    (split : MintClock.splits ≤ φ)
    (chamber : VowsR.Chamber (Tracks.vine (flow C) split) R.kit D Q B)
    (admission : WheelP.Certified R.alloy R.kit) :
    ∃ F, Treehouse.VariableHouse R D Q C B R.family.path.levels.clock.kernel.penalty F
      (stages R.metals.p) := by
  obtain ⟨F,hospital,calendar⟩ := chamber.obligation.1
  have held : VowsR.Chamber (flow C) R.kit D Q B :=
    {chamber with obligation := chamber.obligation.2.2.1.1}
  have spring : Oak.Tutoring.Quarterly R D Q (flow C) B F :=
    ⟨held,chamber.obligation.2.2.1.2,hospital,chamber.obligation.2.2.2.2.1,
      chamber.obligation.2.2.2.2.2,chamber.obligation.2.1,Oak.roll R hG D Q (flow C) B held F hospital⟩
  let t := spring.employed
  let openC : VowsR.Chamber C R.kit D Q B := {t with obligation := t.obligation.1}
  let school : Oak.Tutoring.Quarterly R D Q C B F := {spring with employed := openC}
  let renew := t.obligation.2.2.2
  let rough := t.obligation.2.2.1.1
  let park := t.obligation.2.2.1.2
  have stamps := chamber.obligation.2.2.2.1
  refine ⟨F,on_stages _,rfl,stamps,admission,renew,calendar,school,rough,park,?_⟩
  intro k Sj x d q qV M1 qx ℓq Hc ε zP ηz δ₁ ℓ ℓ' he hp0 he0 hf hd hℓ hη hη' h2 hzp
  exact Boot.Marquee.night R hG D Q C B Sj F school stamps x ℓq d ε ℓ hp0 he0 hℓ renew calendar
    admission Hc zP ηz δ₁ qx hη hf rough park (Boot.Marquee.rook R) h2 hzp he hη' q qV M1 ℓ' hd

theorem selected (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (price : MapPrices), Permitted C s (ThroughLaunch.raging s price)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
        WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ NativeFVAPlateau.Correlations R ∧
        FundedOriginalProperties.{u} hG ε W ∧
        Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨B,store⟩,admission,pace,archive,corr,original,citizen,logBook⟩ :=
    WilsonWindowMarkedChamber.selected.{u} hG hε (Tracks.vine (flow C) split)
      (fun s price => WilsonWindowCourseLaws.physical_course split (external s price))
  obtain ⟨F,H⟩ := house hG R _ _ C B split store admission
  exact ⟨R,T,W,⟨B,F,H⟩,pace,archive,corr,original,citizen,logBook⟩

theorem open_school (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (split : MintClock.splits ≤ φ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        (VowsR.probe G φ) B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
        WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ NativeFVAPlateau.Correlations R ∧
        FundedOriginalProperties.{u} hG ε W ∧
        Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  apply selected hG hε (VowsR.probe G φ) split
  intro s price R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact ⟨V,Push.PriceCompiler.DelayLe.refl _,fun _ _ => trivial⟩

end YM.Integration.WilsonWindowUniversalSchool
end

