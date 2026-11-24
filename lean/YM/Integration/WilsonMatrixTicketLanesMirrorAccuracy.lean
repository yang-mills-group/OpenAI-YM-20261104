import YM.Integration.WilsonMatrixTicketLanesMirrorPrices

/-! Quantitative all-order MS accuracy of the actual finite block-forest coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesMirrorAccuracy
open Filter Lattice FVA2 FVA2.Both.Passage FVA2.Both.Passage.Cohort FormalOPE.RG10.BlockGauge
open MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Menus MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge
open scoped Classical BigOperators
variable {G : Gauge} {B : Deck G} {I J : Type} [LinearOrder J]

/-- The independent complete registered prescription evaluated in the finite forest with all roots marked. -/
def receipts (V : Warehouse G) (P : Trial I J) (A : Prescription B) (μ : ℝ) (w : J → Label B)
    (L : (i : I) → Fabric G (dimT P.side i)) (E : ∀ i, Exhibit (L i)) : Terrify J I :=
  fun s n i => Score.netE (tagPrice (E i) (Label.h ∘ w) (fun j => P.off j i) s
    (Matched.tFees A w) A.team (μ-P.profile.θ i) V (P.head i)) n

/-- The actual finite forest is the same series as the independent mixed-coefficient production. -/
theorem trace (V : Warehouse G) (P : Trial I J) (A : Prescription B) (μ : ℝ) (w : J → Label B)
    (L : (i : I) → Fabric G (dimT P.side i)) (paid : ∀ i, Long (L i))
    (E : ∀ i, Exhibit (L i)) (issued : ∀ i, CapReady.Article V (L i) (E i) (paid i)) :
    receipts V P A μ w L E = MixedStory.ordinary V P A μ w := by
  funext s n i
  exact congrFun (WilsonMatrixTicketLanesMirrorPrices.read (E i) (paid i) V (issued i)
    (Matched.dimT_even P.side i) B s (Label.h ∘ w) (fun j => P.off j i) (P.head i)
    A.team (μ-P.profile.θ i) (Matched.tFees A w)) n

/-- The complete measured field series and the independently fixed MS observable share every filed fee. -/
theorem original (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (h : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) (simple : G.Simple)
    (P : Trial I J) (μ : ℝ) (w : J → Label B) (l : Filter I) (uses : Uses P l μ)
    (L : (i : I) → Fabric G (dimT P.side i)) (paid : ∀ i, Long (L i))
    (E : ∀ i, Exhibit (L i)) (issued : ∀ i, CapReady.Article (WilsonMatrixTicketLanesNativePrices.warehouse R) (L i) (E i) (paid i))
    (s : Finset J) (n : ℕ) :
    let V := WilsonMatrixTicketLanesNativePrices.warehouse R
    PeakT.twin l P.profile mildG (fare (Label.h ∘ w) P.profile (receipts V P A μ w L E) s n)
      (fun i => Dial.tour M w μ (testP P i) s n) := by
  dsimp only
  rw [trace _ P A μ w L paid E issued]
  exact (MixedStory.accuracy M _ P A μ w l (WilsonMatrixTicketLanesMatchedProfiles.original R M A h simple) uses s n).2

end YM.Integration.WilsonMatrixTicketLanesMirrorAccuracy
