import YM.Integration.WilsonMatrixTicketLanesNativeFields
import YM.FVA2.MixedStory
import YM.FVAAlt2.Rocket.Export

/-! The same signed source, matching charges, and MS data throughout both finite-volume prescriptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesMatchedProfiles
open FVA2 MS MS.Local.Physical MS.Menus MS.Wind MS.Land MS.Book.Program
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge
open scoped Classical BigOperators
variable {G : Gauge} {B : Deck G}

private theorem score (V : Warehouse G) (p : Team) {d : ℕ} (A : Acts B d) :
    scoreM (V.native B) p A = scorePl (FVAAlt2.Shop.richBook B V.F V.H V.S V.h V.acts) p A := by
  funext x j
  unfold scoreM scorePl rentM rentPl Glyph.preambleM Glyph.preamblePl
  simp only [WilsonMatrixTicketLanesNativeFields.menu]

/-- Complete interacting position-space field series for the given fees and running team. -/
theorem horizon (V : Warehouse G) (p : Team) {d : ℕ} (A : Acts B d) :
    horizonM (V.native B) p A = horizonPl (FVAAlt2.Shop.richBook B V.F V.H V.S V.h V.acts) p A := by
  funext j
  apply mark_birth (aquaM (V.native B) p A)
    (aquaPl (FVAAlt2.Shop.richBook B V.F V.H V.S V.h V.acts) p A) (k := j+1) _ j (Nat.lt_succ_self _)
  intro i _ x
  exact congrFun (congrFun (score V p A) x) i

/-- The already chosen charges work for the actual registered finite Wilson matrix on R. -/
theorem taylor (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (h : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) :
    TaylorOKM M ((WilsonMatrixTicketLanesNativePrices.warehouse R).native B) A := by
  refine ⟨h.bulk,?_⟩
  intro d i
  rw [horizon]
  exact h.mark d i

/-- All orders and all finite mixed profiles for the very same independently fixed matched scheme. -/
theorem original (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (h : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) (simple : G.Simple) :
    MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) A :=
  MixedStory.ceases M _ (taylor R M A h) simple

end YM.Integration.WilsonMatrixTicketLanesMatchedProfiles
