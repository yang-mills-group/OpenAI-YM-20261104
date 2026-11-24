import YM.MSbar.Domain.Detector
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Modified MS normalization at inverse length one. Hat pairs counted in s = -ε throughout, no
constants implicit in continuation or supplied by matching. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter Complex
open scoped Topology BigOperators Classical ContDiff ENNReal
namespace DR

/-- physical units chosen with μ=1. -/
def ruler := Real.eulerMascheroniConstant - Real.log (4*Real.pi)
def rescale : ℝ := - ruler-2*Real.log (2*Real.pi)
def fixed : ℝ := -4* Real.log (2*Real.pi)
def measure (s:ℂ):ℂ:= Complex.exp (↑fixed + ↑rescale*s)
/-- genuine scalar (when read at integer-pairs workspace count). -/
def mass (m:ℕ) := Real.exp (fixed+rescale*m)
theorem measure_nat (m:ℕ): measure m= (↑(mass m):ℂ):=by unfold measure mass; rw [Complex.ofReal_exp, Complex.ofReal_add, ofReal_mul, ofReal_natCast]
lemma mass_pos (m) : 0<mass m:= Real.exp_pos _
lemma analytic : Differentiable ℂ measure :=by unfold measure; fun_prop

lemma worth {U : Set ℂ}{X:ℕ→Type}{S:Site X}: Eligible U 0 S (fun z _ _=> measure z):= by
    refine ⟨fun _ _ ⦃i j⦄ X x=>rfl,?_⟩; intro E i1 i2 i3 n x h
    refine ⟨(AH.holomorphic (X:=E) isOpen_univ analytic.differentiableOn).upon (subset_univ _), fun _ Q q=>?_⟩; obtain ⟨m,hm⟩:= exists_nat_ge rescale
    refine ⟨0,Real.exp fixed,m,0,(Real.exp_pos _).le,fun z hz v hv=>?_⟩; simp only [Transfer.toll,pow_zero,mul_one,measure,norm_exp, add_re,mul_re, ofReal_im,ofReal_re,zero_mul,sub_zero, ← Real.exp_add]; gcongr
-- scale at s=0. equality to (2π)^(-4). Lib.
lemma ordinary : mass 0=(2*Real.pi)^(-(4:ℝ)):=by
    unfold mass fixed; rw [Real.rpow_def_of_pos (by positivity : (0:ℝ)<2 * Real.pi)]; push_cast; ring_nf
end DR
end YM.MSbar.Domain
