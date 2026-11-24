import YM.Integration.WilsonPositionProgramNestedElection

/-! The position calculation uses the original nested block sizes and their stage floor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmetic
open Filter Lattice RG Wilson RG.Supply Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open OPE OPE.Owl Next.Foundations Roost
open ThroughLaunch Roof Push.PriceCompiler Progress.DirectedRecipe
open WilsonMatrixTicketLengths WilsonMatrixTicketLengthsLender WilsonMatrixTicketFuelPrice
open WilsonLimitConstruction.FundedCompanySelection RegulatorIR
open scoped Classical Topology BigOperators
variable {G:Gauge}

def divides (_simple:G.Simple)(_a:Axis)(_ε:ℝ):Prediction G:=fun {_} {D} {_} _=>
  WilsonPositionProgramLengths.Divisible D

def course (_simple:G.Simple)(_a:Axis)(_ε:ℝ):Prediction G:=fun {M} {D} {_} _=>
  WilsonPositionProgramNestedLengths.Nested D ∧
  ∀ n, WilsonPositionProgramNestedElection.floor G M.p.kernel n ≤ (D.L n).val

theorem prior {M:Metals G}{D:Rolls M.p}{A:Alloy M D}{F:Factor A}{simple:G.Simple}{a:Axis}{ε:ℝ}
    (paid:course simple a ε F):divides simple a ε F:=
  WilsonPositionProgramNestedLengths.divides paid.1

end YM.Integration.WilsonPositionProgramArithmetic
