import YM.Integration.WilsonNeutralCopiedField
import YM.WilsonCoeffUV.Root.UV.Peaks

/-! The independent finite initial table reads the same bare stencil as the
original inverse-fitted Wilson field, in each real component. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralCopiedAngularJet
open Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonNeutralCopiedField
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "F" => R.family.labels.level d
local notation "T" => R.family.localSection d

def reading (w : d < D) (N : ℕ) (n : Side) (j : (F).Index) : Ink (Woods G n) :=
  PowerSeries.X ^ ((F).grades j).2 * flash (jot (brow F (point F 0) D)
    ((Peaks R.family.path.levels R.metals.O T w N N).1 n (point F j)))

theorem one (w : d < D) (N : ℕ) (n : Side) (j : (F).Index) :
    reading R w N n j = jet (Plies T j n) := by
  unfold reading
  rw [Peak_initial]
  have h := herald_lit T w (point F j) n (brow F (point F 0) D)
    (Next.Foundations.valuation G d) R.family.params (R.makes.sections d)
  rw [packBloom, if_pos (show notar F (point F j) = notar F (point F 0) from rfl),
    one_smul] at h
  exact h

/-- The fitted column and physical weights are fixed before choosing a copy.
Every spatial slot, including the constant field, is filed at its raw angular degree. -/
theorem original (w : d < D) (N per : ℕ) (x : R.family.label d)
    (phase : ℂ →ₗ[ℝ] ℝ) (n : Side) :
    jet (fun Y : Lawn (Woods G n) => phase (copied R N per x 0 (mantle Y))) =
      ∑ j, realS (phase (coefficients R N per x j)) * reading R w N n j := by
  let f (j : (F).Index) : Lawn (Woods G n) → ℝ :=
    fun Y => phase (coefficients R N per x j) * Plies T j n Y
  have h : (fun Y : Lawn (Woods G n) => phase (copied R N per x 0 (mantle Y))) = ∑ j, f j := by
    funext Y
    rw [field, map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    let u := coefficients R N per x j
    let b := Plies T j n Y
    change phase (u * (b : ℂ)) = phase u * b
    rw [mul_comm, ← Complex.real_smul, map_smul]
    exact mul_comm ..
  have fg (j : (F).Index) : Green (f j) :=
    contDiffAt_const.mul (innu T R.family.params (R.makes.sections d) j n)
  rw [h,jet_sum Finset.univ f (fun j _ => fg j)]
  apply Finset.sum_congr rfl
  intro j _
  have prod := jet_mul (f := fun _ : Lawn (Woods G n) => phase (coefficients R N per x j))
    (g := Plies T j n) contDiffAt_const (innu T R.family.params (R.makes.sections d) j n)
  rw [jet_const, ← one R w N n j] at prod
  exact prod

end YM.Integration.WilsonNeutralCopiedAngularJet

