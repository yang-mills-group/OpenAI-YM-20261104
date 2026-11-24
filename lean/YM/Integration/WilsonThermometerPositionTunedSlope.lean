import YM.Integration.WilsonThermometerPositionReturnedAxes
import YM.Integration.WilsonPositionProgramSubmittedRate
import YM.Integration.WilsonPositionProgramSubmittedFaces

/-! A cutoff series in each original monetary column, at each genuine placement.
At order one the derivative of that column contributes its own ordinary zeroth
reading next to the original order-one normalized Wilson reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedSlope
open Filter Set Function Finset PowerSeries Lattice RG RG.Supply Org Input
open PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedGeometry WilsonThermometerPositionReturnedAxes
open scoped Classical BigOperators Topology ENNReal

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ)
abbrev Columns := (j : I) → (R.family.labels.level (d j)).Index
def price (v : (j : I) → (R.family.labels.level (d j)).Index → PowerSeries ℂ)
    (b : Columns R d) : PowerSeries ℂ := ∏ j, v j (b j)

def finite (P : XSpace.Period) (z : I → Cover) (tree : P.Tree) (b : Columns R d) : PowerSeries ℂ :=
  PowerSeries.mk fun k => coeff (k + Kick.depthF Finset.univ d b)
    (WilsonPositionProgramCopyTop.normalized R P d z b tree)

/-- The finite-source coefficient series retains the series of the enrolled inverse
on each input before taking a coefficient of the normalized original Wilson program. -/
def paid (v : (j : I) → (R.family.labels.level (d j)).Index → PowerSeries ℂ)
    (M : Columns R d → PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ b, price R d v b * M b

theorem first (v : (j : I) → (R.family.labels.level (d j)).Index → PowerSeries ℂ)
    (M : Columns R d → PowerSeries ℂ) :
    coeff 1 (paid R d v M) =
      ∑ b, (coeff 0 (price R d v b) * coeff 1 (M b) + coeff 1 (price R d v b) * coeff 0 (M b)) := by
  simp only [paid,map_sum,coeff_one_mul,coeff_zero_eq_constantCoeff]
  apply sum_congr rfl
  intro b _
  ring

theorem zeroth (v : (j : I) → (R.family.labels.level (d j)).Index → PowerSeries ℂ)
    (M : Columns R d → PowerSeries ℂ) :
    coeff 0 (paid R d v M) = ∑ b, coeff 0 (price R d v b) * coeff 0 (M b) := by
  simp [paid,coeff_zero_eq_constantCoeff]

/-- Both terms of the first variation are on the original compensated, finite tree,
with the full displacement and the original unit. -/
theorem original (P : XSpace.Period) (z : I → Cover) (tree : P.Tree)
    (D : I → ℕ) (cap : ∀ j, d j < D j)
    (wood : FormalBulk08.Primer.Families R.family) (a : FormalBulk08.City.hue G)
    (digit : I → ∀ i, Site (R.family.S.block i)) (N s : ℕ) (g : ℕ → ℝ)
    (c : (j : I) → (R.family.labels.level (d j)).Index → ℂ)
    (child : (j : I) → FormalBulk08.Dawn.Studio (D j)) :
    let v := fun j => submit (R.family.labels.level (d j)) (cap j) (child j)
      (upper R wood a (cap j) (digit j) N s g (c j))
    coeff 1 (paid R d v (finite R d P z tree)) =
      ∑ b, (coeff 0 (price R d v b) * coeff (1+Kick.depthF Finset.univ d b)
        (WilsonPositionProgramCopyTop.normalized R P d z b tree) +
        coeff 1 (price R d v b) * coeff (Kick.depthF Finset.univ d b)
        (WilsonPositionProgramCopyTop.normalized R P d z b tree)) := by
  intro v
  rw [first]
  simp only [finite,coeff_mk,zero_add]

end YM.Integration.WilsonThermometerPositionTunedSlope
end
