import YM.Integration.WilsonOriginalProjectedCurvatureRender
import YM.Integration.WilsonOriginalProjectedCurvatureProgram

/-! Evaluation and total price of the actual submitted Earn.Row family, in
the regulator and the original fixed registered input of the physical run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureEnrollment
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (σ : ℝ)
  (extra : V → ℕ) (g : ℝ) (x : tastes D) (U : Config G (R.family.side L p))

local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u

def entry (s : Rows) : Poly (Stock.census V) :=
  if h : 0 < wallet Q D u μ orders N s σ then
    let r := WilsonOriginalProjectedCurvatureRender.row Q D u μ orders N s σ (extra s.1.1) h
    Poly.send r.mode (r.nominal g x U)
  else Poly.send ((Stock.census V).fire s.1.1) 0

theorem measured_entry (s : Rows) : entry Q D u μ orders N σ extra g x U s =
    Poly.send ((Stock.census V).fire s.1.1)
      (WilsonOriginalProjectedCurvatureProgram.reading Q D u μ orders N σ g x U s) := by
  unfold entry
  split
  · rename_i h
    dsimp only
    rw [(WilsonOriginalProjectedCurvatureRender.geometry Q D u μ orders N s σ (extra s.1.1) h).1,
      WilsonOriginalProjectedCurvatureRender.submitted,WilsonOriginalProjectedCurvatureProgram.token]
  · rename_i h
    simp only [WilsonOriginalProjectedCurvatureProgram.reading,if_neg h]

def filed : Poly (Stock.census V) :=
  let e := (Fintype.equivFin Rows).symm
  ∑ k : Fin (Fintype.card Rows), entry Q D u μ orders N σ extra g x U (e k)

theorem full : filed Q D u μ orders N σ extra g x U =
    WilsonOriginalProjectedCurvatureProgram.ink Q D u μ orders N σ g x U := by
  unfold filed WilsonOriginalProjectedCurvatureProgram.ink
  exact Finset.sum_congr rfl fun _ _ => measured_entry Q D u μ orders N σ extra g x U _

def booked (w : V → ℝ) :=
  ∑ s : Rows, Poly.toll w ((Stock.census V).fire s.1.1) *
    ‖(Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
      ((grade u s : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) s : ℤ))‖ *
    wallet Q D u μ orders N s σ

theorem cost (hL : L ≤ N) (w : V → ℝ) :
    booked Q D u μ orders N σ w = ActualOriginalQPackets.packetCost Q D u μ orders N w σ := by
  rw [ActualOriginalQCharges.packet_cost D u Q μ orders N hL]
  exact Finset.sum_congr rfl fun s _ => commissioned Q D u μ orders N s σ hL w

theorem original (hL : L ≤ N) :
    filed Q D u μ orders N σ extra (Pert.Asymptotics.regulatorRun R.family N p L) x U =
      Mach (Stock.census V) (fun i =>
        ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i)) := by
  rw [full,WilsonOriginalProjectedCurvatureProgram.measured Q D u μ orders N σ x U hL]

end YM.Integration.WilsonOriginalProjectedCurvatureEnrollment
