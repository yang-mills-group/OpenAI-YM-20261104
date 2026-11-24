import YM.Integration.WilsonOriginalProjectedCurvatureEnrollment
import YM.Integration.WilsonOriginalProjectedCurvatureCredits

/-! Render all original positive-numerical-budget curvature records into the original
earned lamps. The records with zero original budget contribute zero at every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureLamps
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open WilsonOriginalProjectedCurvatureCredits
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ τ : ℝ) (extra : V → ℕ) (w : V → ℝ)

local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "Group" => Funded Q D u μ orders N σ
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L

def cohort (i : Group) : QuadraticLocal.Earn.Row (paper D u) (Stock.census V) G (tastes D) :=
  WilsonOriginalProjectedCurvatureRender.row Q D u μ orders N i.1 σ (extra i.1.1.1) i.2

local notation "X" => cohort Q D u μ orders N σ extra

theorem issued : QuadraticLocal.Earn.Issues X σ (ActualOriginalQLayout.rankCap R u)
    (fun _ => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u) := by
  constructor
  · exact fun i => (WilsonOriginalProjectedCurvatureRender.priced Q D u μ orders N i.1 σ (extra i.1.1.1) i.2).2.1
  · exact fun i => (WilsonOriginalProjectedCurvatureRender.priced Q D u μ orders N i.1 σ (extra i.1.1.1) i.2).2.2

theorem offers (hL : L≤N) (hg : 0<g₀) (hup : g₀≤1) (hw : ∀i,0<w i) :
    QuadraticLocal.Earn.Offers X w τ (invoice Q D u μ orders σ τ extra w) := by
  intro x
  convert offered Q D u μ orders N σ τ extra w hL hg hup hw x using 1
  funext i
  have e := WilsonOriginalProjectedCurvatureRender.geometry Q D u μ orders N i.1 σ (extra i.1.1.1) i.2
  change (if (X i).center=x then Poly.toll w (X i).mode *
    ((X i).salary * Real.exp (τ * ((X i).length:ℝ))) else 0) = _
  simp only [cohort]
  rw [e.1,e.2.1,e.2.2]
  rfl

theorem measured (point : BudgetPoint) (g : ℝ) (x : tastes D) (U : Config G (R.family.side L p)) :
    (∑ i : Group, Poly.send ((QuadraticLocal.Earn.rendered X point g).mode i)
      ((QuadraticLocal.Earn.rendered X point g).nominal x i U)) =
    WilsonOriginalProjectedCurvatureEnrollment.filed Q D u μ orders N σ extra g x U := by
  let E := WilsonOriginalProjectedCurvatureEnrollment.entry Q D u μ orders N σ extra g x U
  have live (i : Group) : Poly.send ((QuadraticLocal.Earn.rendered X point g).mode i)
      ((QuadraticLocal.Earn.rendered X point g).nominal x i U)=E i.1 := by
    simp only [E,WilsonOriginalProjectedCurvatureEnrollment.entry,dif_pos i.2]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => live i)]
  change (∑i : Group, E i.1) = ∑ k : Fin (Fintype.card Rows), E ((Fintype.equivFin Rows).symm k)
  rw [Equiv.sum_comp, ← Finset.sum_subtype (p:=fun i : Rows => 0 < wallet Q D u μ orders N i σ)
    (univ.filter (fun i : Rows => 0 < wallet Q D u μ orders N i σ)) (fun i => by simp) E]
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro i _ h
  have hi : ¬ 0 < wallet Q D u μ orders N i σ := by simpa using h
  simp only [E,WilsonOriginalProjectedCurvatureEnrollment.entry,dif_neg hi,Poly.send_zero]

theorem original (point : BudgetPoint) (x : tastes D) (U : Config G (R.family.side L p)) (hL : L≤N) :
    (∑ i : Group, Poly.send ((QuadraticLocal.Earn.rendered X point g₀).mode i)
      ((QuadraticLocal.Earn.rendered X point g₀).nominal x i U)) =
    Mach (Stock.census V) (fun i =>
      ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
      ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
        (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i)) := by
  rw [measured, WilsonOriginalProjectedCurvatureEnrollment.original Q D u μ orders N σ extra x U hL]

end YM.Integration.WilsonOriginalProjectedCurvatureLamps
