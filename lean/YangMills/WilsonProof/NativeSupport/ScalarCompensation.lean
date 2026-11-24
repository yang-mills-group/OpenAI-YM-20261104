import YangMills.WilsonProof.NativeSupport.CalibratedRead
import YM.MergeProof.Permit

/-! A layer shift can be applied as a native scalar variation and a compensating
fine-field factor. The loop term cancels in the scalar variation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset Lattice Wilson RG
open scoped BigOperators Classical
variable {G : Gauge} {n c : Side}

def actionSlope (R : Rep G n) (U : Config G n) : ℝ :=
  (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed,
    ((∑ f, R.path.baseTerm R.clip R.p (pull s 0 U) f) + ∑ x : Site n,
      (PathData.atomSeries R.path.cubic R.p (pull s 0 U) x +
      PathData.atomSeries R.path.quartic R.p (pull s 0 U) x))

theorem native_action_shift (R : Rep G n) (h : ℝ) (U : Config G n) :
    R.path.inChannels R.clip R.p (R.beta+h) U =
      R.path.inChannels R.clip R.p R.beta U + h*actionSlope R U := by
  let F (s : Signed) := (∑ f, R.path.baseTerm R.clip R.p (pull s 0 U) f) +
    ∑ x : Site n, (PathData.atomSeries R.path.cubic R.p (pull s 0 U) x +
      PathData.atomSeries R.path.quartic R.p (pull s 0 U) x)
  let J (s : Signed) := ∑ x : Site n, PathData.atomSeries R.path.loop R.p (pull s 0 U) x
  let k : ℝ := (Fintype.card Signed : ℝ)⁻¹
  change k*(∑ s, ((R.beta+h)*F s+J s)) = k*(∑ s, (R.beta*F s+J s))+h*(k*∑ s, F s)
  have eq (s : Signed) : (R.beta+h)*F s+J s = (R.beta*F s+J s)+h*F s := by ring
  simp_rw [eq]
  rw [sum_add_distrib, ← mul_sum]
  ring

def atScalar (R : Rep G n) (h : ℝ) : Rep G n := { R with beta := R.beta+h }

theorem compensated_density (R : Rep G n) (h : ℝ) (U : Config G n) :
    Real.exp (h*actionSlope R U) * (atScalar R h).eval U = R.eval U := by
  simp only [Rep.eval, Rep.exponent, atScalar, native_action_shift, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The transition at the changed noise temperature is the genuine transition
at the changed incoming scalar, with its exact input correction. This equality
is on every held field and applies with an arbitrary fine observable. -/
theorem compensated_step (S : StepData c n) (R : Rep G n) (h : ℝ) (f : Config G n → ℝ) :
    S.push (R.beta+h) (fun U => R.eval U*f U) =
      S.push (atScalar R h).beta (fun U => Real.exp (h*actionSlope R U) * (atScalar R h).eval U * f U) := by
  change S.push (R.beta+h) _ = S.push (R.beta+h) _
  simp_rw [compensated_density]

/-- The original capacity inequality is linear in both its multiplicity and
its budget. This is the exact price of storing several dated birth roots above
the same coarse site. -/
theorem palette_multiplicity {P : Pressure.Teller G} {Q : ConnectedActivityE6.Target G P}
    {L : Side} {x a : ℝ} (h : Merge.Palette.shipPrice L Q x 1 a)
    (M : ℕ) (hm : 0 < M) : Merge.Palette.shipPrice L Q x M (a/M) := by
  unfold Merge.Palette.shipPrice at h ⊢
  have nz : (M:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Nat.cast_one,one_mul] at h
  convert h using 1
  field_simp

end YM.Integration.InletSusceptibility
