import YM.Integration.WilsonSurveyedEquationFrameStability

/-! The compensated coordinates of the actual submitted field. The first
identity accounts for every stable-to-primary feed before the report.
The finite-family statement retains one elected course for all uses. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameMeasured
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels XSpace
open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonSurveyedEquationFrameInlet (bank loan price)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} {D h k u e : ℕ} {F : Frame G h} {T : SectionData F} {H : Hol G}

theorem fitted {w : h < D} {rails : Rails h k u e} {A B C E : Credit}
    (X : CutsP H T w rails A B C E) (top : X.N = X.m+X.i) :
    let Q := sectionSeal T w
    let b := projected X.ax X.tx Q X.m X.N k X.pt
    b = ticket X.ax X.tx Q X.N X.m X.N X.tileP ∧
      received X.ax X.tx Q X.m X.N X.N b = X.tileP := by
  let Q := sectionSeal T w
  have date : X.m+X.i ≤ X.N := top.ge
  have count : X.N-X.m = X.i := by omega
  have read := TallOracle X.L X.ha date X.pt X.sp
  have eq : projected X.ax X.tx Q X.m X.N k X.pt =
      ticket X.ax X.tx Q X.N X.m X.N X.tileP := by
    unfold projected ticket
    rw [count]
    exact congrArg (WilsonPositionProgramTrialFittedLens.matrix _) read
  refine ⟨eq,?_⟩
  rw [eq]
  exact (WilsonPositionProgramTrialFittedLens.original H Q X.L.L X.ha (by omega) le_rfl X.tileP).2.1

theorem collective {I : Type*} [Finite I] (R : Run G) (W : Initialize G)
    (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (granted : price W R.kit)
    (h D k u e : I → ℕ) (w : ∀i,h i<D i) (rails : ∀i,Rails (h i) (k i) (u i) (e i))
    (cap : ∀i,capP (deck (G:=G) (fun _ : Fin 1=>h i) (fun _=>D i) (fun _=>w i)) ≤ k i)
    (height : ∀i,h i ≤ k i) :
    ∀ᶠ j:ℕ in atTop, ∀ i m K, j ≤ m → m ≤ K → ∀ b : (loan W (h i) (D i) (w i)).Rider,
      let Q := loan W (h i) (D i) (w i)
      let vote := received R.family.path.levels R.metals.O Q m K K b
      projected R.family.path.levels R.metals.O Q m K (k i)
        (Shrine (plate (bank W (h i)).joined (w i)) vote) = b :=
  Filter.eventually_all.mpr fun i =>
    WilsonSurveyedEquationFrameInlet.original W R simple v funded granted (w i) (rails i) (cap i) (height i)
end YM.Integration.WilsonSurveyedEquationFrameMeasured
