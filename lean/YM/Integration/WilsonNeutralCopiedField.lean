import YM.Integration.WilsonNeutralOffsetCutoff
import YM.WilsonCoeffUV.Root.UV.GaugeSupply

/-! The finite cutoff field retains its numerical source when the auxiliary
period changes. Its actual stencil has the independently filed angular jet
on each of those periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralCopiedField
open Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "F" => R.family.labels.level d
local notation "T" => R.family.localSection d

/-- Freeze the entire cutoff column and its physical units on the original period. -/
def coefficients (N per : ℕ) (x : R.family.label d) : (F).Coeff :=
  ((R.family.S.a N : ℂ) ^ d)⁻¹ • (F).scaled (R.family.path.levels.clock.threshold N)⁻¹
    ((R.family.factory d N per).terminal.symm x)

def copied (N per : ℕ) (x : R.family.label d) {n : Side} (z : Site n)
    (U : Config G n) : ℂ := (T).places (coefficients R N per x) z U

theorem elected (N per : ℕ) (x : R.family.label d) (z : Site (R.family.side N per)) :
    copied R N per x z = R.family.O N per x z := by
  funext U
  unfold copied coefficients SectionData.places Family.O TransferData.cylinder initial
  rw [(T).eval_linear.map_smul]
  rfl

def point (V : Frame G d) (j : V.Index) : Alma V :=
  ⟨(j, ⟨0, by simp⟩), by simpa [rankS] using V.bound j⟩

private theorem basis_real (j : (F).Index) {n : Side} (z : Site n) (U : Config G n) :
    (((T).places (Pi.single j 1) z U).re : ℂ) = (T).places (Pi.single j 1) z U := by
  let y : (F).Coeff := Pi.single j 1
  have e : star y = y := by
    ext i
    by_cases h : i = j
    · subst i; simp [y]
    · simp [y, h]
  have h := (R.makes.sections d).ordinary_real y (expandAt z U)
  have hbar : (T).places y z U = star ((T).places y z U) :=
    (congrArg (fun w : (F).Coeff => (T).places w z U) e.symm).trans h
  have hi := congrArg Complex.im hbar
  change ((T).places y z U).im = -((T).places y z U).im at hi
  apply Complex.ext
  · rfl
  · change 0 = ((T).places y z U).im
    linarith

/-- The very same coefficients, including the unit, multiply the sounded
basis functions on every auxiliary side and at the submitted site. -/
theorem field (N per : ℕ) (x : R.family.label d) {n : Side} (z : Site n) (U : Config G n) :
    copied R N per x z U = ∑ j, coefficients R N per x j *
      (((T).places (Pi.single j 1) z U).re : ℂ) := by
  let v := coefficients R N per x
  let ev : (F).Coeff →ₗ[ℂ] ℂ := (MvPolynomial.aeval (entry (expandAt z U))).toLinearMap.comp (T).evalC
  have split : v = ∑ j, v j • (Pi.single j 1 : (F).Coeff) := by
    ext i; simp [Pi.single_apply, Pi.smul_apply]
  calc copied R N per x z U = ev v := rfl
    _ = ev (∑ j, v j • (Pi.single j 1 : (F).Coeff)) := congrArg ev split
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, basis_real]
      rfl

end YM.Integration.WilsonNeutralCopiedField

