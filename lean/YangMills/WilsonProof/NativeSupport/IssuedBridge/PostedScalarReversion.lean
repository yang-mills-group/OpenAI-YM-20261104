import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedCouplingPowers
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedClockScale
namespace IssuedBridge.PostedScalarReversion
open YM YM.XSpace YM.MS YM.FVA2 YangMills.MSbar PowerSeries
open scoped BigOperators Classical
noncomputable section
theorem original (p : Book.Program.Cn) (a : ℕ → ℝ)
    (read : ∀ k, coeff k p = (a k : ℂ)) (start : a 0 = 0) (lead : a 1 = 1) (k : ℕ) :
    coeff k (Reg.Token.back p) = ((Series.inverseCoupling a k : ℝ) : ℂ) := by
  let f := Series.inverseCoupling a
  let q : Book.Program.Cn := mk (fun i => (f i : ℂ))
  have issued (j : ℕ) : coeff j q = (f j : ℂ) := coeff_mk ..
  have hp : coeff 0 p = 0 := by rw [read, start, Complex.ofReal_zero]
  have h₁ : coeff 1 p = 1 := by rw [read, lead, Complex.ofReal_one]
  have hq : coeff 0 q = 0 := by
    rw [issued]
    change ((Series.inverseCoupling a 0 : ℝ) : ℂ) = 0
    rw [Series.inverseCoupling_zero, Complex.ofReal_zero]
  have joined : p.subst q = X := by
    apply PowerSeries.ext
    intro n
    rw [FPS.coeff_substituted _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans hq)]
    calc
      (∑ j ∈ Finset.range (n+1), coeff j p • coeff n (q^j)) =
          ((∑ j ∈ Finset.range (n+1), a j * YangMills.Matching.couplingPower f j n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [read, Complex.ofReal_mul]
        exact congrArg (fun v : ℂ => (a j : ℂ) * v) (PostedCouplingPowers.original q f issued j n)
      _ = coeff n X := by
        rw [show (∑ j ∈ Finset.range (n+1), a j * YangMills.Matching.couplingPower f j n) = _ from
          Series.coupling_after_inverse a start lead n, coeff_X]
        split_ifs <;> rfl
  have equal : q = Reg.Token.back p :=
    Reg.Token.paid _ (Reg.Token.both (Reg.Token.covers p hp h₁)) joined hq
  rw [← equal]
  exact issued k
end
end IssuedBridge.PostedScalarReversion
