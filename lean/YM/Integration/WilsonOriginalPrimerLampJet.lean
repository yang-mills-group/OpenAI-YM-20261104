import YM.QuadraticLocal.Poetry.Helmet
import YM.X.Gauss.Hook

/-! A raw curvature word, measured along an arbitrary analytic link ray,
has exactly its filed angular grade after the original common source power
is cleared. The vanishing of the low curvature ranks also handles lamps
whose nominal coupling grade lies above the requested coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerLampJet
open Function Filter Finset Lattice Laurent RG Wilson Stationary
open QuadraticLocal QuadraticLocal.Poetry PositionX.Jet PositionX.Gauss AllOrder AllOrder.Fire
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink
open AllOrder.Ink.Method Stationary
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{M:Type}[Fintype M][DecidableEq M]{n:Side}

theorem earned (p:Lantern G M)(x:Site n)(v:AllOrder.Ker.rule M n)
    (l d j:ℕ)(rank:p.r≤l+d+1)
    (f:ℝ→Link G n)(hf:ContDiffAt ℝ ω f 0):
    someJ (fun t:ℝ=>t^(l+d+1-p.r)*p.light x (Haiku.life f t) v) (j+d+1)=
    weigh f (Lantern.gleam p x v l) j:=by
  let F:=fun z:Link G n=>p.light x (Stationary.input G n z) v
  have smooth:ContDiffAt ℝ ω F 0:=(Helmet.frameGrade p.atom x|>.smooth).mul contDiffAt_const
  have curve:ContDiffAt ℝ ω (F ∘ echo f) 0:=by
    have e0:echo f 0=0:=by simp [echo]
    exact (e0 ▸ smooth).comp 0 (contDiffAt_id.smul hf)
  have low (k:ℕ)(h:k<p.r):Radial.jet F k=0:=by
    unfold F
    rw [Lantern.frame_cross,show Radial.jet (Helmet.frame p.atom x) k=0 from
      funext fun y=>(Helmet.frameGrade p.atom x).jet_z y h,smul_zero]
  change someJ ((fun t:ℝ=>t^(l+d+1-p.r))*(F ∘ echo f)) (j+d+1)=_
  rw [jo_shift curve, Lantern.arc p x v l f hf j]
  by_cases hj:l≤j
  · rw [if_pos hj,if_pos (show l+d+1-p.r≤j+d+1 by omega)]
    simp only [show j+d+1-(l+d+1-p.r)=j-l+p.r by omega]; rfl
  rw [if_neg hj]
  split <;> rename_i h
  · rw [weigh_curved smooth hf]
    unfold weigh
    apply Finset.sum_eq_zero
    intro k hk
    rw [low k (by have:=Finset.mem_range.mp hk; omega)]
    simp [Function.comp_def,someJ]
  rfl

end YM.Integration.WilsonOriginalPrimerLampJet
end
