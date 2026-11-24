import YM.Integration.WilsonOriginalMixedGaussianTable
import YM.Integration.WilsonOriginalRegisteredFoldedDrivers

/-! Removing the common vacuum from an entire ordinary squarefree roster at finite grading order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrdinaryFactor
open Primitives.GCC.Anchor Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonVacuumPreResetFiniteRegister WilsonOriginalMixedGaussianTable
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {V ι S:Type}[Fintype V][DecidableEq V][Fintype ι][DecidableEq ι]
  (J:Census V)(r:ℕ)(B:S→ℝ)(a:ι→Poly J)(T:Finset ι→Ink S)(vacuum:Ink S)

omit [Fintype V] [Fintype ι] in
private theorem empty_part {s:Finset ι}(live:s.Nonempty)(hot:∀j,(a j).part J.quiet=0):
    (∏ j∈s,a j).part J.quiet=0:=by
  obtain ⟨j,hj⟩:=live
  rw [← Finset.mul_prod_erase s a hj,Poly.quiet_mul,hot,zero_mul]

theorem denominator_of_roster (empty:T ∅=1)(hot:∀j,(a j).part J.quiet=0):
    denominator (stock J r B (fun s:Finset ι=>∏j∈s,a j) T)=1:=by
  classical
  unfold denominator stock
  rw [map_sum,Finset.sum_eq_single ∅]
  · simp [term,empty]
  · intro s _ ne
    apply Join.both_parts
    intro t u
    rw [bottom_value,term_value,empty_part J a (Finset.nonempty_iff_ne_empty.mpr ne) hot]
    simp
  · simp

theorem cancel (head:constantCoeff vacuum=1)(empty:T ∅=1)(hot:∀j,(a j).part J.quiet=0):
    ratio (stock J r B (fun s:Finset ι=>∏j∈s,a j) (fun s=>vacuum*T s))=
      stock J r B (fun s:Finset ι=>∏j∈s,a j) T:=by
  classical
  let z:=register J r (observed B vacuum)
  let U:=stock J r B (fun s:Finset ι=>∏j∈s,a j) T
  have factor:stock J r B (fun s:Finset ι=>∏j∈s,a j) (fun s=>vacuum*T s)=z*U:=by
    unfold U stock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [term,z,map_mul]
    ring
  have unit:z.part (Board J r).quiet=1:=by
    rw [←Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
    simp [OriginalRadialSeries.observed,Census.quiet,coeff_zero_eq_constantCoeff_apply,head]
  have den:denominator (z*U)=z:=by
    change bottom J r (z*U)=z
    rw [map_mul,WilsonOriginalRegisteredFoldedDrivers.vacant]
    change z*denominator U=z
    rw [denominator_of_roster J r B a T empty hot,mul_one]
  rw [factor,ratio,den]
  calc
    z*U*inverseMass z=(z*inverseMass z)*U:=by ring
    _=U:=by rw [right_inverse unit,one_mul]

end YM.Integration.WilsonReceivedDepositedOrdinaryFactor

