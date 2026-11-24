import YM.Integration.WilsonMacroscopicRichFixedDecoder
import YM.Integration.WilsonMacroscopicRichDescentPosterior

/-! The same positive-height fixed-scale reading as a physical conditional at every lower configuration. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichReportedPosterior
open Function Filter Set MeasureTheory Lattice Wilson RG Cells Extraction OPE PhysMS Spec
open RG16 RG16.Literal MergeProof MergeProof.Accent Trace.Physical.GermGraph
open RGComparison.Core16 PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) {N p u : ℕ}

/-- The full normalized observation includes the engineering factor of the genuine coarse credit. -/
def observation (T : Slices R.family.path.levels p) (live : u ≤ N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (V : Config G (R.family.side u p)) : ℂ :=
  (R.family.S.a u : ℂ)^h * (traversal T live).conditioned (line R.family.path p u N) Y V

theorem density (T : Slices R.family.path.levels p) (live : u ≤ N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (V : Config G (R.family.side u p)) :
    credit R.family N p h Y u live V =
      ((R.family.path.rep N p u).eval V : ℂ) * observation R T live h Y V := by
  let D := traversal T live
  let β := line R.family.path p u N
  have target : β D.depth = R.family.beta N p := bare_beta T live
  have joint : (fun U => (bare (R.family.beta N p) U : ℂ) * Y U) =
      (bare (β D.depth) : Config G (R.family.side N p) → ℝ) • Y := by
    rw [target]
    funext U
    rfl
  have vac : D.vacuum (G:=G) β V = (R.family.path.rep N p u).eval V :=
    congrFun (vacuum_eq T R.makes.wilson live) V
  have nz : ((R.family.path.rep N p u).eval V : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (vac ▸ (Descent.positive β (traversal_ok T live) V).ne')
  unfold credit
  rw [joint,WilsonMacroscopicRichDescentPosterior.output R.family.path p T live]
  change _ * D.weighted β Y V = _ * (_ * (D.vacuum β V)⁻¹ • D.weighted β Y V)
  rw [vac,Complex.real_smul,Complex.ofReal_inv]
  field_simp

/-- The booked sheet is the very numerator of the physical finite forest on every held field. -/
theorem issued (T : Slices R.family.path.levels p) (live : u ≤ N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (door : Opened R.family h u p)
    (held : Booked R.family N p h Y u live) :
    let q := sheet R.family N p h Y u live
    let M := topReport R.family N p h R.makes u door live Y
    ∃ a : ℝ, reads h N p u q a ∧
      (∀ V, value (C:=R.family) h N p u q V = ((R.family.path.rep N p u).eval V : ℂ) * observation R T live h Y V) ∧
      fitting h N p u R.makes door live M = page h p u q := by
  obtain ⟨a,formed,exactly⟩ := held.sheet R.family N p h
  refine ⟨a,formed,fun V => (congrFun exactly V).symm.trans (density R T live h Y V),?_⟩
  exact (fitting h N p u R.makes door live).apply_symm_apply _

end YM.Integration.WilsonMacroscopicRichReportedPosterior
