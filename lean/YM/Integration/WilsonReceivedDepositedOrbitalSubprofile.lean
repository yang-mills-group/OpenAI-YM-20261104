import YM.Integration.WilsonReceivedDepositedOrbitalGrade

/-! A particular set of inherited pages retains its own complete conditional
programme. The connected observation uses only its proper submoments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalSubprofile
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue PowerSeries Extra.Trajectories
open WilsonReceivedDepositedOrbitalMode (face)
open WilsonReceivedDepositedOrbitalColumns (row)
open WilsonReceivedDepositedOrbitalGrade (booked thermal at_row earnings restrict)
open WilsonVacuumPreResetFiniteRegister (register)
open scoped Classical BigOperators
variable {V α U:Type}[Fintype V][DecidableEq V][DecidableEq α]
local notation "J" => Stock.census V
variable (f:α↪V)(r:ℕ)(B:U→ℝ)(w:V→ℂ)
  (M:Finset V→Ink U)(N L:Finset α→Ink U)(file:∀s,M (s.map f)=N s)
  (law:Equation N L)

include file law in
theorem on_rows (s:Finset α):
    row (connected (booked r B w M)) (s.map f)=(∏u∈s,w (f u)) • thermal V r B (L s):=by
  let X:=booked r B w M
  have blank:M ∅=1:=(by simpa only [Finset.map_empty] using (file ∅).trans law.1)
  have unit:row X ∅=1:=by rw [show X=_ from rfl,at_row,blank,prod_empty,one_smul,map_one]
  have inherited:=restrict f (WilsonReceivedDepositedOrbitalEquation.original X unit)
  have receipt:=earnings (fun u=>w (f u)) (law.mapKin (thermal V r B))
  have proper: (fun u=>row X (u.map f))=(fun s=>(∏u∈s,w (f u)) • thermal V r B (N s)):=by
    funext j
    rw [show X=_ from rfl,at_row,file,Finset.prod_map]
  rw [proper] at inherited
  letI : IsAddTorsionFree (Poly (indices r)):=.of_isTorsionFree ℂ (Poly (indices r))
  exact congrFun (Equation.unique _ _ _ inherited receipt) s

include file law in
theorem observed (s:Finset α)(d:ℕ)(kept:d≤r):
    (Order.observe (J) r (connected (booked r B w M)) d).part (face (s.map f))=
      (∏u∈s,w (f u))*(MvPolynomial.eval B (coeff d (L s)):ℝ):=by
  have eq:=congrArg (fun z:Poly (indices r)=>z.part (pick r d)) (on_rows f r B w M N L file law s)
  change (connected (booked r B w M)).part (Join.pair (face (s.map f)) (pick r d))=
    (∏u∈s,w (f u))*(register (J) r (PowerSeries.map (MvPolynomial.eval B) (L s))).part
      (Join.pair (J).quiet (pick r d)) at eq
  rw [WilsonVacuumPreResetFiniteRegister.read,if_pos rfl,picked r kept,coeff_map] at eq
  unfold Order.observe
  rw [if_pos kept,Poly.part_smul]
  change (d.factorial:ℂ)⁻¹*(connected (booked r B w M)).part (Join.pair (face (s.map f)) (pick r d))=_
  rw [eq]
  have nonzero:(d.factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero d
  field_simp

end YM.Integration.WilsonReceivedDepositedOrbitalSubprofile
end
