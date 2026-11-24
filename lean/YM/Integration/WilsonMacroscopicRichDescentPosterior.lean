import YM.RGComparison.Core16.Trajectory
import YM.Integration.WilsonMacroscopicRichCaptureRoots

/-! The measured certificate and the compact-forest experiment have the same
   full Wilson numerator, lower field and positive vacuum on the enrolled path. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichDescentPosterior
open Function MeasureTheory Lattice RG Wilson Push.GridApprox OPE OPE.Therm
open RGComparison.Core16 PhysicalNext.Repeat.Legato WilsonMacroscopicForwardTransfer
open private steps from YM.Integration.WilsonMacroscopicRichCaptureRoots
open scoped Topology
variable {G : Gauge}

theorem output (H : History G) (p : ℕ) (T : Slices H.levels p) {u N : ℕ} (h : u ≤ N)
    (f : Config G (H.S.side N p) → ℂ) :
    pushTo H N p h f = (traversal T h).output (line H p u N) f := by
  induction h using Nat.decreasingInduction with
  | self => rw [pushTo_self, traversal_self, Descent.output_nil]
  | of_succ u hu ih =>
    rw [← steps H N p (Nat.le_succ u) hu f, pushTo_next H N p le_rfl, pushTo_self, ih,
      traversal_push T hu, Descent.output_push, next_line]
    rfl

/-- Every physically held field sees the complete tested numerator under the
    original finite forest. The path uses the actual temperature at each step. -/
theorem measured (R : Run G) {N p u : ℕ} (T : Slices R.family.path.levels p) (h : u ≤ N)
    (X : Config G (R.family.side N p) → ℂ) (V : Config G (R.family.side u p)) :
    exterior (C := R.family) (N := N) h X V =
      (traversal T h).conditioned (line R.family.path p u N) X V := by
  let A := R.family.path
  let D := partition G (A.S.side N p) (A.β N p N)
  let d := traversal T h
  let β := line A p u N
  have dpos : D ≠ 0 := (partition_pos _).ne'
  have den : d.vacuum (G := G) β V = (A.rep N p u).eval V :=
    congrFun (vacuum_eq T R.makes.wilson h) V
  have mass : (A.rep N p u).eval V ≠ 0 := den ▸ (Descent.positive β (traversal_ok T h) V).ne'
  have fc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr dpos
  have vc : ((A.rep N p u).eval V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr mass
  have pay : WilsonMacroscopicForwardTransfer.weighted (C := R.family) (N := N) X =
      D⁻¹ • ((bare (β d.depth) : Config G (A.S.side N p) → ℝ) • X) := by
    funext U
    have top : (A.rep N p N).eval U = bare (A.β N p N) U := congrFun (R.makes.wilson.starts N p).2 U
    have tip : β d.depth = A.β N p N := bare_beta T h
    change (((A.rep N p N).eval U / D : ℝ) : ℂ) * X U =
      D⁻¹ • (bare (β d.depth) U • X U)
    rw [top, tip, Complex.real_smul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
    ring
  have all : pushTo A N p h (WilsonMacroscopicForwardTransfer.weighted (C := R.family) (N := N) X) =
      D⁻¹ • d.weighted β X := by
    rw [output A p T h, pay, Descent.output_smul_real_const]
    rfl
  change pushTo A N p h (WilsonMacroscopicForwardTransfer.weighted (C := R.family) (N := N) X) V /
    (((A.rep N p u).eval V / D : ℝ) : ℂ) = (d.vacuum β V)⁻¹ • d.weighted β X V
  rw [all, den, Pi.smul_apply, Complex.real_smul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_inv]
  field_simp

end YM.Integration.WilsonMacroscopicRichDescentPosterior
