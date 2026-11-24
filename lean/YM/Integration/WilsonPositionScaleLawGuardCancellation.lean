import YM.Integration.WilsonPositionScaleLawGuardSubstitute

/-! Central polynomial evaluation of a formal conjugacy in a noncommutative
normed algebra, including the genuine scalar reparametrization. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardCancellation
open Finset PowerSeries MS.Book.Program
open WilsonPositionScaleLawGuardPoly (Same value mass)
open WilsonPositionScaleLawGuardSubstitute (composed system)
open scoped Polynomial Classical BigOperators
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

abbrev print (q:ℕ)(a:PowerSeries R):R[X]:=trunc (q+1) a
def fringe (q:ℕ)(ψ:PowerSeries ℂ)(A H N B:PowerSeries R):R[X]:=
  print q B*composed q (trunc (q+1) ψ) A-print q H*print q N

theorem original (q:ℕ)(ψ:PowerSeries ℂ)(root:Rooted ψ)(A H N B:PowerSeries R)(law:H*N=B*system ψ A)
    {z:ℂ}(hz:‖z‖≤1):
    ‖value (print q B) z*value (print q A) ((trunc (q+1) ψ).eval z)-
      value (print q H) z*value (print q N) z‖≤‖z‖^(q+1)*mass (fringe q ψ A H N B):=by
  have rhs:Same q (print q B*composed q (trunc (q+1) ψ) A) (H*N):=by
    rw [law]
    exact WilsonPositionScaleLawGuardPoly.product (WilsonPositionScaleLawGuardPoly.issued q B)
      (WilsonPositionScaleLawGuardSubstitute.issued (WilsonPositionScaleLawGuardPoly.issued q ψ) root A)
  have lhs:=WilsonPositionScaleLawGuardPoly.product (WilsonPositionScaleLawGuardPoly.issued q H)
    (WilsonPositionScaleLawGuardPoly.issued q N)
  rw [←WilsonPositionScaleLawGuardSubstitute.printedAt,←WilsonPositionScaleLawGuardPoly.multiply,
    ←WilsonPositionScaleLawGuardPoly.multiply]
  exact WilsonPositionScaleLawGuardPoly.cost rhs lhs hz

end YM.Integration.WilsonPositionScaleLawGuardCancellation
