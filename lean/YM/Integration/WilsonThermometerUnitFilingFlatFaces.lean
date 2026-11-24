import YM.Integration.WilsonThermometerUnitFilingFlatPupil
import YM.Integration.WilsonReceivedIdentityField

/-! All true thermometric face bills enter the one ordinary compensated endpoint, on its receiving radii. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatFaces
open Function Finset Lattice RG Wilson Marker Ac QuadraticLocal Earn
open Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Primitives.GCC.Anchor
open WilsonThermometerCenteredAlgebra
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V χ ι:Type} [DecidableEq V] {R:Census V} {p:BudgetPoint} {o:V → Site n}

theorem unmasked (L:Lamps χ ι G p o R) (x:χ) : L.log x (1:Config G n)=
    WilsonRootedKioskOccupiedSlip.bare L x (1:Config G n):=by
  unfold Lamps.log WilsonRootedKioskOccupiedSlip.bare
  apply tsum_congr
  intro i
  have clear:Healthy p.threshold (L.ground i) (1:Config G n):=by unfold Healthy;rw [UVNext.CouplingReset.flags_one];simp
  have same:=WilsonRootedKioskOccupiedSlip.healthy L x i (1:Config G n) clear
  unfold WilsonRootedKioskOccupiedSlip.gap at same
  rw [sub_eq_zero] at same
  exact congrArg (Poly.send (L.mode i)) same

local notation "J" => Stock.census (Fin 3)
theorem complete (w:Fin 3 → ℝ) (pos:∀v,0<w v) {g:ℝ} (gp:0<g) (cool:g≤1)
    (U Z Q:Poly J) (s:(J).Mode) (bill:ℝ) (faces:∀t:(J).Mode,Poly.toll w t*‖U.part t-Z.part t‖≤bill):
    Poly.toll (fun v=>g*w v) s*‖(total U Q).part s-(total Z Q).part s‖ ≤
      ((Fintype.card (J).Mode:ℝ)*bill)*Poly.price (fun v=>g*w v) (inverseMass Q):=by
  let v:=fun i=>g*w i
  have funded:∀i,0<v i:=fun i=>mul_pos gp (pos i)
  have smaller (t:(J).Mode):Poly.toll v t≤Poly.toll w t:=by
    apply prod_le_prod (fun a _=>(funded a).le)
    intro a _
    exact (mul_le_mul_of_nonneg_right cool (pos a).le).trans_eq (one_mul _)
  have store:Poly.price v (U-Z)≤(Fintype.card (J).Mode:ℝ)*bill:=by
    calc _≤∑_t:(J).Mode,bill:=by
          apply sum_le_sum
          intro t _
          exact (mul_le_mul_of_nonneg_right (smaller t) (norm_nonneg _)).trans (faces t)
        _=_:=by simp
  change Poly.toll v s*‖((U*inverseMass Q)-(Z*inverseMass Q)).part s‖≤_
  rw [←sub_mul]
  exact (Poly.member funded _ _).trans ((Poly.multiplication funded _ _).trans
    (mul_le_mul_of_nonneg_right store (Poly.nonnegative funded _)))

end YM.Integration.WilsonThermometerUnitFilingFlatFaces
