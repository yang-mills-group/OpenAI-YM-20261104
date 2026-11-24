import YM.Integration.WilsonWindowJointPurchase
import YM.RemainderComparison.Lyric.Orbit

/-! A pre-block floor reserving one eighth of the original fine support exponent
for a marked hard component on the elected Wilson factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowOriginalHardRadius

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Lattice RG Wilson Pressure ThroughLaunch WilsonLimitConstruction.FundedCompanySelection
open Push.PriceCompiler ConnectedActivityE6
open RemainderComparison.Lyric
open scoped Classical

variable {G : Gauge}

/-- The incoming exponent here is the one quoted by the actual target. -/
def Fee {P : Teller G} (Q : Target G P) (L : Side) : Prop :=
  radiusCost Q L (P.top.supportExponent-P.top.supportExponent/8)

theorem before_block {P : Teller G} (Q : Target G P) :
    ∃ n : ℕ, ∀ L : Side, n≤L.val → Fee Q L := by
  exact bidLift (Q:=Q) (b:=Q.ε) (by linarith only [Q.grants.1,Q.usable]) Q.usable

def Booked : Prediction G := fun {M} {_} {_} F =>
  ∀ j i, StepStages j i → ∀ L : Side, M.p.floorL j ≤ L.val → Fee (F.target j i) L

theorem allPrices : WilsonFundedWindowMenu.AllPrices (@Booked G) := by
  intro s M target expenses flags programs wages baton
  choose n pay using fun (j i : ℕ) => before_block (target j i)
  refine ⟨fromMax n,?_⟩
  intro l hl rolls wage duration register post scouts pocket protection stages cost menu V small
  refine ⟨V,Push.PriceCompiler.DelayLe.refl _,?_⟩
  intro W' hW bar wait priced directed archive origin rank
  dsimp only
  intro η q exchange names rebates booth shelter works divides j i adjacent L large
  exact pay j i L ((le_fromMax n adjacent).trans ((hl j).trans large))

theorem on_roll (R : Run G) (paid : Booked R.kit) (j i : ℕ) (adjacent : StepStages j i) :
    Fee (R.kit.target j i) (R.rolls.L j) :=
  paid j i adjacent (R.rolls.L j) (R.rolls.large j).need


end YM.Integration.WilsonWindowOriginalHardRadius
