import YM.Integration.WilsonOriginalProjectedCurvatureBudget

/-! The complete incoming registered source assembled from the paid Haar-invariant
curvature tensors. The independent tests and physical configuration are shared by
all genuine rows, including the identically vanishing zero-fee rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureProgram
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureRoster WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvatureBudget
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (σ : ℝ)
  (g : ℝ) (x : tastes D) (U : Config G (R.family.side L p))

local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) x

def reading (s : Rows) : ℂ :=
  if 0 < wallet Q D u μ orders N s σ then
    (g : ℂ) ^ ((grade u s : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) s : ℤ)) *
      (((divided (placed u s) σ).unmasked U (ActualRunQlocalNativeTuple.root D s.1.1) : ℂ) *
        paint Q D u μ orders N s σ x)
  else 0

omit [DecidableEq V] [Fintype V] in
theorem token (s : Rows) : reading Q D u μ orders N σ g x U s =
    (g : ℂ) ^ (-(ActualRunKernelPackets.fieldRank R (degree u) s : ℤ)) *
      (ActualOriginalQPackets.token Q D u μ orders N s).read test U := by
  unfold reading
  split
  · rename_i h
    rw [phase,work Q D u μ orders N s σ x U (substantial Q D u μ orders N s σ h)]
  · rename_i h
    rw [unfunded Q D u μ orders N s σ (not_lt.mp h) x U,mul_zero]

def ink : Poly (Stock.census V) :=
  let e := (Fintype.equivFin Rows).symm
  ∑ k : Fin (Fintype.card Rows),
    Poly.send ((Stock.census V).fire (e k).1.1) (reading Q D u μ orders N σ g x U (e k))

theorem submitted : ink Q D u μ orders N σ g x U =
    (ActualOriginalQPackets.packets Q D u μ orders N).read test g U := by
  unfold ink ActualOriginalQPackets.packets
  rw [MarkedPackets.ofFin_read]
  exact Finset.sum_congr rfl (fun k _ => congrArg _ (token Q D u μ orders N σ g x U _))

theorem measured (hL : L ≤ N) :
    ink Q D u μ orders N σ (Pert.Asymptotics.regulatorRun R.family N p L) x U =
      Mach (Stock.census V) (fun i =>
        ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i)) := by
  rw [submitted,ActualOriginalQPackets.packets_read Q D u μ orders N hL]

end YM.Integration.WilsonOriginalProjectedCurvatureProgram
