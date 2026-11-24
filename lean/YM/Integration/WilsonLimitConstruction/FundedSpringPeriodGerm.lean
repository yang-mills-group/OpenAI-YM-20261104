import YM.Integration.FundedInteractingPeriod
import YM.Integration.WilsonLimitConstruction.FundedSpringCoverRegrade

/-! The formal numerator of the signed finite period plan under the actual
inverse-temperature regrading, including the main term, the physical loop
and every submitted native analytic curvature packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringPeriodGerm
open Function Filter Matrix Lattice Laurent Bloch Wilson RG Precision Exterior Stationary PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FreeResolvent
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (n : Side)

def packets (a : Cost) (Z : SeriesA G) : Ink (Woods G n) :=
  (Z.map fun v=> (soil a*X)^(v.grade-v.rise)*jet (turnSeries v.cells (m:=n))).sum

private theorem packets_regraded {a : Cost} (ha : constantCoeff a=1) (Z : SeriesA G) :
    redo a (FundedPeriodAction.formal n Z)=packets n a Z := by
  induction Z with
  | nil => simp [FundedPeriodAction.formal,packets]
  | cons v Z ih =>
    change redo a (X^(v.grade-v.rise)*jet (turnSeries v.cells (m:=n))+
      FundedPeriodAction.formal n Z)=
        (soil a*X)^(v.grade-v.rise)*jet (turnSeries v.cells (m:=n))+packets n a Z
    rw [map_add,map_mul,map_pow,redo_X,redo_jet a ha,ih]

theorem grade (B : Clip) (P : PathData G) (Z : SeriesA G) :
    shellK 2 (front P B n+sands Z n) := by
  apply shell_sum _ (sand_span Z n)
  intro k l h
  simp only [front,Pi.add_apply,(sprig_count _ 2) k l h,
    (sprig_count _ 0) k l (by omega),add_zero]

/-- Exact formal charged polynomial for the real Plan on the prescribed
original finite torus and genuine positive branch. The scalar factor is
kept on the curvature-packet numerator itself. -/
theorem original (B : Clip) (P : PathData G) {s A L : ℝ} (hp : P.Bounds B s A L)
    (Z : SeriesA G) {σ C : ℝ} (hs : 0<σ) (hZ : Draw Z σ C)
    {p : Cost} (unit : constantCoeff p=1) :
    X^2*flash (Blue.mix (pace p) (front P B n+sands Z n)) =
      soil p*jet (fun w : TreeVars G n => mainTerm B P (mantle w))+
      X^2*jet (fun w : TreeVars G n=> Precision.loop P (mantle w))+
      soil p*packets n (pace p) Z := by
  let a := pace p
  have ua : constantCoeff a=1 := pace_cc unit
  have balance : (soil (U:=Woods G n) p)*(soil a)^2=1 := by
    rw [←map_pow,←map_mul,pace_tax unit,map_one]
  have shift : (soil (U:=Woods G n) p)*(soil a*X)^2=X^2 := by
    rw [mul_pow,←mul_assoc,balance,one_mul]
  have h := congrArg (redo a) (FundedInteractingPeriod.series B P hp Z hs hZ n)
  simp only [map_add,map_mul,map_pow,redo_X,redo_stern a (grade n B P Z),redo_jet a ua,
    packets_regraded n ua] at h
  calc
    _ = soil p*((soil a*X)^2*flash (Blue.mix a (front P B n+sands Z n))) := by rw [←mul_assoc,shift]
    _ = _ := by rw [h,mul_add,mul_add,←mul_assoc,shift]

end YM.Integration.WilsonLimitConstruction.FundedSpringPeriodGerm
