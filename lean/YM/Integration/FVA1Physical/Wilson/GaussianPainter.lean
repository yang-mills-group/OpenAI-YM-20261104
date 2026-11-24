import YM.Integration.FVA1Physical.Wilson.GaussianEntrance

/-! The next finite-period normalized Wilson kernel at leading order takes
the true connected marked Gaussian expectation of the emitted painter.
The conditional covariance, drift and vacuum normalization all come from
the chosen next forest and Wilson kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Lattice RG Exterior Tree Precision Marker Multi
open YM.Next.SectorChange YM.Extra.Trajectories Comparison.RG02 Assembly Order
open scoped Topology Classical ContDiff BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f} {C : Clip} {P : PathData G}
    {O : ChartRatio G} {I : Type} [Fintype I] [DecidableEq I] {R : Census I}
    (K : Bulk.Kernel S C P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (hw : Bulk.Well W) (x : fieldDir G c 1)
local notation "μ" => Gaussian.cloud (K.covariance F t)
local notation "draw" => Bulk.translated K F x
local notation "M" => Bulk.markFn S F W
local notation "A" => Bulk.geometric K F t W

include hw
theorem gaussian_rows_zero (z : Key F G → ℝ) (u : R.Mode) :
    rows (expansions W.power M A) u 0 (draw z) =
    (Poly.pass (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2)).part u := by
  let y:=draw z
  have time : y.1=1 := congrArg Prod.fst (Bulk.footing K F x z)
  let a:=affine W.power M A y
  let bank:=QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F y).2
  have seed : PowerSeries.coeff 0 a = bank := by
    change PowerSeries.coeff 0 (realCurve R (vacuumLetter A y) + curve W.power M y) = _
    rw [map_add,realCoeff,curve,PowerSeries.coeff_mk]
    have vac : vacuumLetter A y 0=0 := rfl
    rw [vac,Complex.ofReal_zero,map_zero,zero_add]
    change lit R _ = lit R _
    apply congrArg (lit R)
    funext m
    exact (leading_painter F W hw m y time).trans (part_lit _ m)
  let hsym:Symmetric (series R 0 a):=Symmetric.known _
  have lift:=exponent_identity (r:=0) W.power M A y
  have run:=congrArg First.buc lift
  rw [First.buc_pass hsym (driver_quiet W.power M A y 0)] at run
  change observe R 0 (series R 0 _) 0 = Poly.pass (observe R 0 (series R 0 _) 0) at run
  rw [observation _ _ _ (Nat.zero_le 0),observation _ _ _ (Nat.zero_le 0)] at run
  exact congrArg (fun v:Poly R=>v.part u) (run.trans (congrArg Poly.pass seed))

def gaussianLamp : Poly R := fun u=> ∫ z, (Poly.pass
    (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2)).part u ∂μ

theorem physical_gaussian_moments (r : ℕ) :
    First.buc (Bulk.Fk K F t W x r) = gaussianLamp K F t W x := by
  ext1 u
  have one:=observed (x:=Bulk.Fk K F t W x r) u (Nat.zero_le r)
  rw [Bulk.table,picked r (Nat.zero_le r)] at one
  simp only [Nat.factorial_zero,Nat.cast_one,one_mul] at one
  exact one.trans (integral_congr_ae (Filter.Eventually.of_forall fun z=>gaussian_rows_zero K F t W hw x z u))

theorem physical_gaussian_connected (r : ℕ) :
    First.buc (logMarked (Bulk.Fk K F t W x r)) = connected (gaussianLamp K F t W x) := by
  rw [Cumulants.orphan (Bulk.fk_sym K F t W x r) (Bulk.fk_unit K F t W x r),physical_gaussian_moments K F t W hw]

theorem gaussian_single_integrand (z : Key F G → ℝ) (i : I) :
    rows (expansions W.power M A) (R.fire i) 0 (draw z) =
    (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).part (R.fire i) := by
  rw [gaussian_rows_zero K F t W hw]
  let v:=QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2
  have h : v.part R.quiet=0 := part_lit_quiet _
  exact (Cumulants.lamp i (Poly.pass v) (Poly.pass_part v h)).symm.trans
    (congrArg (fun a:Poly R=>a.part (R.fire i)) (Cumulants.connected_pass h))

theorem gaussian_single_integrable (i : I) :
    Integrable (fun z=> (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).part (R.fire i)) μ := by
  have hm:= (gather (r:=0) (Bulk.stage K F x) (Bulk.hinge F) W.power M A (K.covariance F t)
    (K.symm F t) (K.positive F t) (R.fire i) (pick 0 0)).1
  rw [picked 0 (Nat.zero_le 0)] at hm
  exact hm.congr (Filter.Eventually.of_forall fun z=>gaussian_single_integrand K F t W hw x z i)

theorem physical_gaussian_single (r : ℕ) (i : I) :
    (First.buc (logMarked (Bulk.Fk K F t W x r))).part (R.fire i) =
      ∫ z, (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).part (R.fire i) ∂μ := by
  rw [physical_gaussian_connected K F t W hw,Cumulants.lamp]
  · apply integral_congr_ae
    filter_upwards with z
    let v:=QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2
    have h : v.part R.quiet=0 := part_lit_quiet _
    exact (Cumulants.lamp i (Poly.pass v) (Poly.pass_part v h)).symm.trans
      (congrArg (fun a:Poly R=>a.part (R.fire i)) (Cumulants.connected_pass h))
  · rw [←physical_gaussian_moments K F t W hw x r,First.buc_vac]
    exact Bulk.fk_unit K F t W x r

end YM.Integration.FVA1Physical.Wilson
