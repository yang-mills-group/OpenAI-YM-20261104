import YM.Integration.WilsonOriginalProjectedCurvatureAtom
import YM.QuadraticLocal.Earn.Passport

/-! Each deposited measured-coupling token has a genuine invariant manuscript atom
with its original paths, color salary, and exact finite numerical reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureRoster
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
  (s : Row (R:=R) u)

def placed : Atom G (ActualRunKernelPackets.tokenRank R (degree u) s) :=
  WilsonOriginalProjectedCurvatureAtom.atom (fun k => (word s.2.2.val k).2)
    (fun k => (ActualRunCurvaturePackets.ofRun R (degree u s.1)).data.columns
      s.2.1 (word s.2.2.val k).1)

omit [DecidableEq V] [Fintype V] in
theorem lawful : (placed u s).Invariant :=
  WilsonOriginalProjectedCurvatureAtom.invariant _ _

omit [DecidableEq V] [Fintype V] in
theorem charges : (placed u s).length = ActualOriginalQCharges.rowFall u s ∧
    (placed u s).magnitude = ActualOriginalQCharges.tensorMass u s :=
  ⟨rfl,WilsonOriginalProjectedCurvatureAtom.magnitude _ _⟩

omit [DecidableEq V] [Fintype V] in
theorem paid :
    (placed u s).magnitude *
      ‖MvPolynomial.coeff s.2.2.val
        ((ActualRunCurvaturePackets.ofRun R (degree u s.1)).data.shape s.2.1)‖ *
      readerPrice D s.1.1 * ‖coordinates (R:=R) u s.1 s.2.1‖ =
    ActualOriginalQCharges.rowMass D u s := by
  rw [(charges u s).2]
  rfl

omit [DecidableEq V] [Fintype V] in
theorem actual (N : ℕ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    (ActualOriginalQPackets.token Q D u μ orders N s).read x U =
      (((placed u s).unmasked U (ActualRunQlocalNativeTuple.root D s.1.1) : ℝ) : ℂ) *
        ActualRunKernelPackets.amplitude R (ActualRunQlocalNativeTuple.orbit D) (degree u)
          N p L (labels Q D u μ orders N) s x := by
  unfold placed
  rw [WilsonOriginalProjectedCurvatureAtom.unmasked]
  apply NativeCurvatureTensor.token_read

end YM.Integration.WilsonOriginalProjectedCurvatureRoster
