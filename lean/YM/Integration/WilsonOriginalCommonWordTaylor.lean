import YM.Integration.WilsonOriginalClusteredAxialDirection

/-! The two complete words use the same actual small field.  Both the values and the
jets of the discarded part are returned to the original estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCommonWordTaylor
open Lattice RG Wilson Comparison.Density.Transport AnalyticBridge.SectorAffine.Offset
open scoped ContDiff
variable {G:Gauge}{n:Side}

/-- Numerical value of a finite roster after separating its short and long group words. -/
theorem original (f short tail:Config G n→ℂ)(U:Config G n)(X:Directions G n)
    {w high low far outside:ℝ}{l J:ℕ}(order:l ≤ J)(pos:0<w)(small:w ≤ 1)(bound:‖X‖ ≤ w)
    (nonneg:0 ≤ low)(eqn:f=short+tail)(move:short (increment 1 X)=short U)
    (salary:∀A,‖A‖ ≤ w→Through J (short ∘ increment 1) A high)
    (smooth:ContDiffAt ℝ J (f ∘ increment 1) 0)
    (jets:∀i<l,‖iteratedFDeriv ℝ i (f ∘ increment 1) 0‖ ≤ low)
    (long:Through J (tail ∘ increment 1) 0 far)(gross:‖tail U‖ ≤ outside):
    ‖f U‖ ≤ (l:ℝ)*(low+far)+high*w^l+outside:=by
  have diff:short ∘ increment 1=f ∘ increment 1 - tail ∘ increment 1:=by
    ext A
    have split:=congrFun eqn (increment 1 A)
    change f (increment 1 A)=short (increment 1 A)+tail (increment 1 A) at split
    change short (increment 1 A)=f (increment 1 A)-tail (increment 1 A)
    rw [split,add_sub_cancel_right]
  have atzero (i:ℕ)(hil:i<l):‖iteratedFDeriv ℝ i (short ∘ increment 1) 0‖ ≤ low+far:=by
    have depth:=hil.le.trans order
    rw [diff,iteratedFDeriv_sub_apply (smooth.of_le (mod_cast depth)) (through_le long depth).smooth]
    exact (norm_sub_le ..).trans (add_le_add (jets i hil) (long.pay i depth))
  have paid:0 ≤ high:=(salary 0 (by simpa only [norm_zero] using pos.le)).nonneg
  let Y:=w⁻¹ • X
  have normY:‖Y‖ ≤ 1:=by
    rw [show ‖Y‖=w⁻¹*‖X‖ by rw [show Y=w⁻¹ • X from rfl,norm_smul,Real.norm_of_nonneg (inv_pos.mpr pos).le]]
    exact (inv_mul_le_iff₀ pos).2 (by simpa only [mul_one] using bound)
  have undo:dilation (Directions G n) w Y=X:=by
    change w • (w⁻¹ • X)=X
    rw [smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
  have val:=through_value (rescale l J w high (low+far) (short ∘ increment 1) pos.le small
    paid (add_nonneg nonneg long.nonneg) order salary atzero Y normY)
  simp only [Function.comp_apply,undo,move] at val
  rw [eqn,Pi.add_apply]
  exact (norm_add_le ..).trans (add_le_add val gross)

end YM.Integration.WilsonOriginalCommonWordTaylor
end
