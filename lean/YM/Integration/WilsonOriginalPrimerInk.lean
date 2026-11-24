import YM.Integration.WilsonElectedPrimaryCurvature
import YM.WilsonCoeffUV.Step.Unshifted

/-! Re-express the independently normalized primary's torus tensors in
the components used by the finite marked Wilson conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerInk
open Function Finset Lattice Laurent RG Wilson FormalBulk08
open FormalBulk08.Mesa FormalBulk08.Orb FormalBulk08.Reef FormalBulk08.Lava FormalBulk08.Kemp
open FormalBulk08.Lotus Stationary WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}

def column (d:ℕ)(T:Pot G)(n:Side):PChart G n:=fun e r=>
  if r≤d+e then sand (sieve n (T e r)) else 0

theorem span (d:ℕ)(T:Pot G)(n:Side):shellK d (column d T n):=by
  intro e r h
  rw [column,if_neg (not_le.mpr h)]

theorem symmetric (d:ℕ)(T:Pot G)(n:Side)(e:ℕ):Pure (column d T n e):=by
  intro r
  by_cases allowed:r≤d+e
  · rw [column,if_pos allowed]
    exact fun σ x=>agate_sand _ x σ
  rw [column,if_neg allowed]
  exact Smooth.zero

private theorem paint_facade {I:Type}[Fintype I](r:ℕ)(T:Lava.Tile I r):
    Blue.paint r T=Lava.facade r T:=by
  change (∑x:Fin r→I,T x • ∏i,MvPolynomial.X (x i))=_
  rw [facade_eq]
  simp only [MvPolynomial.smul_eq_C_mul,cards]

/-- The whole filed angular polynomial, including its scalar and every
positive rank, agrees at every coupling grade. -/
theorem original (d:ℕ)(T:Pot G)(n:Side):
    flash (column d T n)=Kemp.banner d T n:=by
  apply PowerSeries.ext
  intro e
  rw [Blue.flash,Kemp.banner,coeff_mk,coeff_mk,visible (n:=d+e+1)
    (fun r hr=>span d T n e r (by omega))]
  apply sum_congr rfl
  intro r hr
  have permit:r≤d+e:=Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [column,if_pos permit,paint_facade,sand_facade]

end YM.Integration.WilsonOriginalPrimerInk
end
