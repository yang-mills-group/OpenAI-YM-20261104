import YM.Integration.FVA1Physical.Wilson.GaussianPainter
import YM.Comparison.RG02.Thermal.Wick

/-! The first positive coupling order of every physical marked mode, with
the complete incoming action and the exact finite-volume vacuum subtraction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Lattice RG Exterior Tree Precision Marker Multi
open YM.Primitives.GCC.Anchor YM.Next.SectorChange YM.Extra.Trajectories Comparison.RG02 Assembly Order
open scoped Topology Classical ContDiff BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} {C:Clip} {P:PathData G}
    {O:ChartRatio G} {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
    (K:Bulk.Kernel S C P O) (F:Forest S.ratio) (t:S.Choices)
    (W:Bulk.Colors R G f) (hw:Bulk.Well W) (x:fieldDir G c 1)
local notation "μ" => Gaussian.cloud (K.covariance F t)
local notation "draw" => Bulk.translated K F x
local notation "M" => Bulk.markFn S F W
local notation "A" => Bulk.geometric K F t W

/-- All marked order-one vertices and the exact cubic action with Haar and loop terms. -/
def firstVertices (z:Key F G→ℝ):Poly R :=
  Poly.bead R (-(Complex.ofReal (jet A 3 (draw z)))) +
  lit R (fun i=>jet (M i) (W.power i+1) (draw z))

def firstMoment:Poly R := fun s=>
  ∫ z,((firstVertices K F t W x z)*
    (QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).pass).part s ∂μ

include hw
theorem physical_rows_first (z:Key F G→ℝ) (s:R.Mode):
    rows (expansions W.power M A) s 1 (draw z) =
    ((firstVertices K F t W x z)*(QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).pass).part s := by
  let y:=draw z
  let a:=affine W.power M A y
  let bank:=QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F y).2
  have time:y.1=1:=congrArg Prod.fst (Bulk.footing K F x z)
  have h0:PowerSeries.coeff 0 a=bank:=by
    change PowerSeries.coeff 0 (realCurve R (vacuumLetter A y)+curve W.power M y)=_
    rw [map_add,realCoeff,curve,PowerSeries.coeff_mk]
    have vac:vacuumLetter A y 0=0:=rfl
    rw [vac,Complex.ofReal_zero,map_zero,zero_add]
    change lit R _=lit R _;apply congrArg (lit R);funext i
    exact (leading_painter F W hw i y time).trans (part_lit _ i)
  have h1:PowerSeries.coeff 1 a=firstVertices K F t W x z:=by
    change PowerSeries.coeff 1 (realCurve R (vacuumLetter A y)+curve W.power M y)=_
    rw [map_add,realCoeff,curve,PowerSeries.coeff_mk]
    simp only [vacuumLetter,one_ne_zero,↓reduceIte,Complex.ofReal_neg,firstVertices,markLetter]
    rfl
  have run:=congrArg First.ind (exponent_identity (r:=1) W.power M A y)
  rw [First.ind_pass (by decide) (Symmetric.known _) (driver_quiet W.power M A y 1)] at run
  change observe R 1 (series R 1 _) 1 = observe R 1 (series R 1 a) 1*Poly.pass (observe R 1 (series R 1 a) 0) at run
  rw [observation _ _ _ (le_refl 1),observation _ _ _ (le_refl 1),observation _ _ _ (Nat.zero_le 1),h0,h1] at run
  exact congrArg (fun v:Poly R=>v.part s) run

theorem physical_first_moments (r:ℕ) (pos:0<r):
    First.ind (Bulk.Fk K F t W x r) = firstMoment K F t W x := by
  ext s
  have e:=observed (x:=Bulk.Fk K F t W x r) s (show 1≤r from pos)
  rw [Bulk.table,picked r (show 1≤r from pos)] at e
  simp only [Nat.factorial_one,Nat.cast_one,one_mul] at e
  exact e.trans (integral_congr_ae (Eventually.of_forall fun z=>physical_rows_first K F t W hw x z s))

omit hw in
theorem physical_first_centered (std:W.Standard) (r:ℕ) (pos:0<r):
    First.ind (logMarked (Bulk.Fk K F t W x r)) =
      firstMoment K F t W x*inverseMass (gaussianLamp K F t W x) -
      Poly.bead R (-(Complex.ofReal (Thermal.Layers.forecast K F t x 1))) := by
  have vac:=(Thermal.Wick.pays_first K F t W std x pos)
  rw [Order.Second.grade] at vac
  rw [First.first_log pos (Bulk.fk_sym ..) (Bulk.fk_unit ..)]
  rw [show (First.ind (Bulk.Fk K F t W x r)).part R.quiet=_ from vac,
    physical_first_moments K F t W std.1 x r pos,physical_gaussian_moments K F t W std.1]
end YM.Integration.FVA1Physical.Wilson
