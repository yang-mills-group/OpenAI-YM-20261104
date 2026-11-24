import YM.Integration.WilsonOriginalProjectedCurvaturePointCredit

/-! The rooted point registration is financed before all periods, periods' sites,
orders within the fixed ceiling, coupling cutoffs and reporting scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureClock
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open WilsonOriginalProjectedCurvatureCredits
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (J : Request V)
  (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)
  (μ : ℝ) (σ τ : ℝ) (extra : V → ℕ) (w : V → ℝ)
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u

def charge : ℝ := ∑s : Rows, ActualOriginalQCharges.rowPrice D₁ u w (σ+τ) s *
  Real.exp (τ * (liftHeight D₁ u s extra : ℝ))

theorem quoted (K : ℕ) (hw : ∀i, 0<w i) :
    ∃C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ N : ℕ, ∀orders : V→ℕ, (∀i,orders i≤K) →
      invoice Q D₁ u (μ-R.family.S.scale N) orders σ τ extra w ≤
        (C*(1+‖R.family.S.scale N‖)^b)*charge R J u σ τ extra w := by
  obtain ⟨C,hC,b,h⟩ := ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  refine ⟨C,hC,b,?_⟩
  intro N orders ho
  rw [charge, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  unfold WilsonOriginalProjectedCurvatureCredits.quoted
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (h s.1.1 (orders s.1.1) (ho _) s.1.2 (R.family.S.scale N))
    (mul_nonneg (ActualOriginalQCharges.row_price_nonneg D₁ u w (σ+τ) hw s) (Real.exp_pos _).le)

theorem offered (K : ℕ) (hw : ∀i, 0<w i) :
    ∃C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ (N p L : ℕ) (o : V → Site (R.family.side L p))
      (orders : V→ℕ), (∀i,orders i≤K) → L≤N →
      0<Pert.Asymptotics.regulatorRun R.family N p L →
      Pert.Asymptotics.regulatorRun R.family N p L ≤ 1 →
      ∀x : Site (R.family.side L p),
      let D := ActualOriginalQPointSetup.pointDatum R J p L o
      let η := μ-R.family.S.scale N
      SumBudget (fun i : Funded Q D u η orders N σ =>
        if ActualRunQlocalNativeTuple.root D i.1.1.1=x then
          Poly.toll w ((Stock.census V).fire i.1.1.1) * gross Q D u η orders N i.1 σ τ extra
        else 0) ((C*(1+‖R.family.S.scale N‖)^b)*charge R J u σ τ extra w) := by
  obtain ⟨C,hC,b,h⟩ := quoted R J Q u μ σ τ extra w K hw
  refine ⟨C,hC,b,?_⟩
  intro N p L o orders ho hL hg hup x
  have e := WilsonOriginalProjectedCurvaturePointCredit.offered R J Q u p L o
    (μ-R.family.S.scale N) orders N σ τ extra w hL hg hup hw x
  exact ⟨e.1,e.2.1,e.2.2.trans (h N orders ho)⟩

end YM.Integration.WilsonOriginalProjectedCurvatureClock
