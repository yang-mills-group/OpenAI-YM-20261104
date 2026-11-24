import YM.RG05Readout.Pulse.Excursion

/-! The full translated ultraviolet constellation at an arbitrary earlier
physical cell. The same displacement acts on every original insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredOrbit
open Function Set MeasureTheory Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G) {I:Type} [Fintype I] [DecidableEq I] {N p k:ℕ}

theorem original (D:I→ℕ) (v:(i:I)→Palette C (D i)) (r:ℝ) (Ψ:Wave I) (top:k≤N) {cap B:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (room:r*cap+2*C.S.a k<C.S.radius p)
    (far:B+r*cap<C.S.radius p) (m:ℕ) (o:Site (C.side k p)) (inside:∀z∈Native.box,‖voyager C p k o z‖≤B)
    (g:Body) (U:Config G (C.side N p)):
    constellation D v r Ψ top m g (Lattice.pull 1 ((C.S.toDepth top p).embed o) U)=
      ∫z in Native.box,g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*multi C m N p D v (rel r Ψ (voyager C p k o z)) U):=by
  let V:=Lattice.pull 1 ((C.S.toDepth top p).embed o) U
  let h (y:I→Site (C.side k p)) (z:E4):=g.val z*scalp D v y top (cropX Ψ y r z) V
  have row (y:I→Site (C.side k p)): IntegrableOn (h y) Native.box:=meet_lives D v r Ψ top y g V
  have point (z:E4) (hz:z∈Native.box):g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*multi C m N p D v (rel r Ψ (voyager C p k o z)) U)=
      premiums C D m k r *∑y:I→Site (C.side k p),h y z:=by
    rw [Pulse.car (C:=C) D v r Ψ top rp enclosed room far m o z hz (inside z hz)]
    simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,stepUp,Motion.scalar,premiums,Finset.prod_mul_distrib]
    dsimp only [h,V];rw [←Finset.mul_sum];simp only [Bool.false_eq_true, ite_false];ring
  rw [setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet point,integral_const_mul,
    integral_finsetSum _ (fun y _=>row y)]
  unfold constellation meet
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  rfl

end YM.Integration.WilsonPositionSeparatedProfileCenteredOrbit
