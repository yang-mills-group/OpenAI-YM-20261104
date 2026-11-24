import YM.Integration.ActualNormalizedPush
import YM.Push.BETA_TRANSPORT.Block
import YM.Push.BETA_TRANSPORT.Noise

/-! Exact log ratio of the full normalized physical conditional at one
fixed held field, with a positive chart density at both fine fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalConditionalFactors
open RG Wilson Lattice Push.BetaTransport
variable {G:Gauge}

theorem factors {a b k l u v w:ℝ} (ha:0<a) (hb:0<b) (hk:0<k) (hl:0<l) (hu:0<u) (hv:0<v) (hw:0<w) :
    Real.log ((a*(k*u/w))/(b*(l*v/w)))=Real.log (a/b)+Real.log (k/l)+Real.log (u/v) := by
  rw [Real.log_div (mul_pos ha (div_pos (mul_pos hk hu) hw)).ne' (mul_pos hb (div_pos (mul_pos hl hv) hw)).ne',
    Real.log_mul ha.ne' (div_pos (mul_pos hk hu) hw).ne',Real.log_mul hb.ne' (div_pos (mul_pos hl hv) hw).ne',
    Real.log_div (mul_pos hk hu).ne' hw.ne',Real.log_div (mul_pos hl hv).ne' hw.ne',
    Real.log_mul hk.ne' hu.ne',Real.log_mul hl.ne' hv.ne',Real.log_div ha.ne' hb.ne',
    Real.log_div hk.ne' hl.ne',Real.log_div hu.ne' hv.ne'];ring

theorem original (C:Family G) (made:C.Makes) (N per m:ℕ) (hm:m<N) (V:Config G (C.side m per))
    (X Y:Config G (C.side (m+1) per)) (a b:ℝ) (ha:0<a) (hb:0<b) :
    let S:=C.path.levels.clock.op m per
    let β:=C.path.β N per (m+1)
    let Q:=C.path.rep N per (m+1)
    Real.log ((a*actualConditionalDensity C N per m V X)/(b*actualConditionalDensity C N per m V Y))=
      Real.log (a/b)+Real.log (S.density β X V/S.density β Y V)+Real.log (Q.eval X/Q.eval Y) := by
  let S:=C.path.levels.clock.op m per
  let β:=C.path.β N per (m+1)
  have kernel (U:Config G (C.side (m+1) per)) : 0<S.density β U V :=
    (inv_pos.mpr (noiseCost_pos S |β|)).trans_le (density_bounds S (C.path.levels.blocks m per).branches le_rfl U V).1
  apply factors ha hb (kernel X) (kernel Y)
    (Multi.AxisShift.chosen_positive made.wilson hm X) (Multi.AxisShift.chosen_positive made.wilson hm Y)
    (Multi.AxisShift.chosen_positive made.wilson hm.le V)

end YM.Integration.WilsonLocalConditionalFactors
