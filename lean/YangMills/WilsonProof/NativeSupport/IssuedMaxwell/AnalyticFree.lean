import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleCalibration
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.AnalyticFree
open YM YM.Maxwell YM.Tensor YM.Analysis YM.Maxwell.WaveOn
open scoped Topology ContDiff
variable {G:Gauge} {j l:ℕ} {x:E4}
theorem green (hx:x≠0):ContDiffAt ℝ ω Green x:=by
  unfold Green
  have hw:=norm_pos_iff.mpr hx
  exact contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.inv (by dsimp;positivity))
theorem first (hx:x≠0)(i:Axis):ContDiffAt ℝ ω (grad i Green) x:=
  grad_smooth i (green hx) (by simp)
theorem curl (hx:x≠0)(a k m:Axis):ContDiffAt ℝ ω (curlOpp a k m) x:=by
  unfold curlOpp
  split_ifs <;> exact ContDiffAt.sub (by first | apply first hx | exact contDiffAt_const) (by first | apply first hx | exact contDiffAt_const)
theorem bare (hx:x≠0)(a b k m:Axis):ContDiffAt ℝ ω (bareCurl a b k m) x:=
  (grad_smooth a (curl hx b k m) (by simp)).sub (grad_smooth b (curl hx a k m) (by simp))
theorem differential {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f:YM.Maxwell.Field F}
    (hf:∀a b,ContDiffAt ℝ ω (f a b) x)(j:ℕ):ContDiffAt ℝ ω (nth f j) x:=by
  refine contDiffAt_pi.mpr fun a=>contDiffAt_pi.mpr fun b=>?_
  exact (show ContDiffAt ℝ ω (fun _:E4=>(Nat.factorial j:ℝ)⁻¹) x from contDiffAt_const).smul
    ((hf a b).iteratedFDeriv_right (i:=j) (m:=ω) (by simp))
theorem body (hx:x≠0)(P:Extended G j)(a b:Axis):ContDiffAt ℝ ω (responded G P a b) x:=by
  unfold responded
  apply ContDiffAt.sum
  intro c _
  have hL:ContDiffAt ℝ ω (scalarTest P c a b) x:=by
    let L:=P.toContinuousLinearMap
    exact L.contDiff.contDiffAt.comp x (differential (f:=leftF G c a b)
      (fun i l=>(tint (G:=G) (unitColor G c)).contDiff.contDiffAt.comp x (bare hx i l a b)) j)
  exact hL.smul contDiffAt_const
theorem original (p:Probe G j)(q:Probe G l)(hx:x≠0):ContDiffAt ℝ ω (legKernel p q) x:=by
  let L:=(extension q).toContinuousLinearMap
  exact contDiffAt_const.mul (L.contDiff.contDiffAt.comp x (differential (fun i k=>body hx (extension p) i k) l))
end IssuedMaxwell.AnalyticFree
end
