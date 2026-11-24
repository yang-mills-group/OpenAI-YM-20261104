import YM.Integration.WilsonMacroscopicRichReportedPosterior
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Line

/-! Entire physical, coarse-field derivatives of a booked source with every regular summand. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichReportedRays
open Function Filter Set Lattice Wilson RG Source Analysis MergeProof.Accent RG16 RG16.Literal
open RGComparison.Core16 PhysicalNext.Repeat.Legato ProjectorNext.Equivariance Trace.Physical
open Trace.Physical.GermGraph Next.Foundations Push.Local
open private ray_sum from YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Line
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (R : Run G) {N p u : ℕ}

def ray {n : Side} (k : ℕ) (A : Directions G n) (f : Config G n → ℂ) : ℂ :=
  iteratedDeriv k (fun t : ℝ => f (increment 1 (t • A))) 0

/-- A true local chart equality and all its affine-ray derivatives on the same finite Wilson forest. -/
theorem original (T : Slices R.family.path.levels p) (live : u ≤ N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (door : Opened R.family h u p)
    (held : Booked R.family N p h Y u live) :
    let q := sheet R.family N p h Y u live
    let V := R.family.path.rep N p u
    let visible := (R.family.localSection h).places ((R.family.labels.level h).scaled V.p.threshold⁻¹ q.x) 0
    let full := WilsonMacroscopicRichReportedPosterior.observation R T live h Y
    (full-visible =ᶠ[𝓝 (1 : Config G (R.family.side u p))] fun U => ∑' i, q.regular i U) ∧
    ∀ A : Directions G (R.family.side u p), ∀ k, k ≤ V.p.order →
      HasSum (fun i => ray k A (q.regular i)) (ray k A (full-visible)) := by
  let q := sheet R.family N p h Y u live
  let V := R.family.path.rep N p u
  let B := R.family.localSection h
  let full := WilsonMacroscopicRichReportedPosterior.observation R T live h Y
  let core : Config G (R.family.side u p) → ℂ := B.places ((R.family.labels.level h).scaled V.p.threshold⁻¹ q.x) 0
  obtain ⟨r,formed,book,_⟩ := WilsonMacroscopicRichReportedPosterior.issued R T live h Y door held
  have visible : (full-core) =ᶠ[𝓝 (1 : Config G (R.family.side u p))] fun U => ∑' i, q.regular i U := by
    filter_upwards [offFlags V.p.threshold V.p.threshold_pos] with U quiet
    have eq := book U
    change q.density 0 B V U = (V.eval U : ℂ) * full U at eq
    rw [noFlagCharge q 0 B (R.makes.sections h) quiet] at eq
    have sum : core U + ∑' i,q.regular i U = full U := mul_left_cancel₀ (noFlagEval quiet) eq
    change full U-core U=∑' i,q.regular i U
    rw [←sum]; abel
  refine ⟨visible,fun A k hk => ?_⟩
  obtain ⟨_,_,_,_,_,_,⟨e,fee,spent⟩,_⟩ := formed.2
  have bill : Summable e := fee.2.1.of_nonneg_of_le (fun i => (spent i).1)
    (fun i => V.p.loMass _ _ (spent i).1)
  exact ray_sum formed.1.smooth spent bill visible A k hk

end YM.Integration.WilsonMacroscopicRichReportedRays
