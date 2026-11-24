import YM.Integration.WilsonThermometerPositionTunedChange
import YM.Integration.WilsonThermometerPositionTunedObserved

/-! First signed perturbative reading of the actual cutoff inverse and the
public fields on its same admitted basis. Keep the derivative of the submitted
coefficients on the full correlated ground, including in the changed field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedCorrection
open Function Lattice Wilson Labels Source Source.Drops XSpace RegulatorIR.FVAAlt2
open PhysicalNext.Repeat.Legato WilsonPositionProgramSubmittedGeometry
open WilsonThermometerPositionReturnedAxes WilsonThermometerPositionTunedSlope
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G) {I:Type} [Fintype I] [LinearOrder I]
variable (d:I→ℕ) (P:XSpace.Period) (z:I→ Cover) (T:P.Tree)

def surveyed (b:Columns R d) : PowerSeries ℂ :=
  Bare.normalized T G (WilsonThermometerPositionTunedChange.earned R W P T d z b)

def residual (b:Columns R d) : PowerSeries ℂ := PowerSeries.mk fun k =>
  PowerSeries.coeff (k+Kick.depthF Finset.univ d b) (Bare.normalized T G
    (Taylor.expandTaylor (T.basis G) (WilsonThermometerPositionTunedChange.change R W P T d z b)))

theorem face (b:Columns R d) :
    finite R d P z T b - surveyed R W d P z T b = residual R W d P z T b := by
  apply PowerSeries.ext
  intro k
  have h:=congrArg (PowerSeries.coeff (k+Kick.depthF Finset.univ d b))
    (WilsonThermometerPositionTunedChange.signed R W P T d z b)
  rw [map_sub,PowerSeries.coeff_X_pow_mul',if_pos (by omega),Nat.add_sub_cancel] at h
  simpa only [map_sub,finite,surveyed,residual,PowerSeries.coeff_mk] using h

variable (v:(j:I)→(R.family.labels.level (d j)).Index→PowerSeries ℂ)

/-- Read the entire changed source on the original normalized mesh before
estimating it. Its zero and first order see the actual cutoff coefficient. -/
theorem earned :
    paid R d v (finite R d P z T) - paid R d v (surveyed R W d P z T) =
      paid R d v (residual R W d P z T) := by
  simp only [paid,← Finset.sum_sub_distrib,← mul_sub,face R W d P z T]

theorem first :
    PowerSeries.coeff 1 (paid R d v (finite R d P z T)) -
      PowerSeries.coeff 1 (paid R d v (surveyed R W d P z T)) =
    ∑ b, (PowerSeries.coeff 0 (price R d v b) * PowerSeries.coeff 1 (residual R W d P z T b) +
      PowerSeries.coeff 1 (price R d v b) * PowerSeries.coeff 0 (residual R W d P z T b)) := by
  rw [← map_sub,earned,WilsonThermometerPositionTunedSlope.first]

/-- The weights here are the original inverse-normalized marked cutoff study and
its actual distinct child sections. -/
theorem original (D:I→ℕ) (cap:∀j,d j<D j) (wood:FormalBulk08.Primer.Families R.family)
    (hue:FormalBulk08.City.hue G) (digit:I→∀i, Site (R.family.S.block i))
    (N s:ℕ) (g:ℕ→ℝ) (c:(j:I)→(R.family.labels.level (d j)).Index→ℂ)
    (child:(j:I)→FormalBulk08.Dawn.Studio (D j)) :
    let submitted:=fun j=>submit (R.family.labels.level (d j)) (cap j) (child j)
      (upper R wood hue (cap j) (digit j) N s g (c j))
    PowerSeries.coeff 1 (paid R d submitted (finite R d P z T)) -
      PowerSeries.coeff 1 (paid R d submitted (surveyed R W d P z T)) =
      ∑ b, (PowerSeries.coeff 0 (price R d submitted b) * PowerSeries.coeff 1 (residual R W d P z T b) +
        PowerSeries.coeff 1 (price R d submitted b) * PowerSeries.coeff 0 (residual R W d P z T b)) :=
  first R W d P z T _

end YM.Integration.WilsonThermometerPositionTunedCorrection
end
