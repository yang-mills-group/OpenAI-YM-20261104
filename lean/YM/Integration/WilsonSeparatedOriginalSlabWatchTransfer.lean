import YM.Integration.WilsonMacroscopicRichSingleWatch

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchTransfer
open Function Filter Set MeasureTheory Spec OPE OPE.Orbits Lattice Wilson Next.UVStress
open WilsonMacroscopicRichWatchLaw WilsonMacroscopicRichWatchLabels
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

def contrast (W:Watch C){h:ℕ}(p:ℕ×ℕ)(Y:C(Config G (C.side p.1 p.2),ℂ))(z:C.label h):ℂ:=
  meter C W (Y-source C h p.1 p.2 z)

theorem physical (W:Watch C){h:ℕ}(p:ℕ×ℕ)(Y:C(Config G (C.side p.1 p.2),ℂ))(z:C.label h):
    contrast W p Y z=Wilson.moment (C.beta p.1 p.2) (fun U=>(Y U-C.O p.1 p.2 z 0 U)*W.plot p.1 p.2 U):=same C W _

theorem cost (F:Final C f S)(W:Watch C)(h:ℕ):∃K:ℝ,0<K ∧ ∀ᶠp in f.fuse,
    ∀(Y:C(Config G (C.side p.1 p.2),ℂ))(x z:C.label h),
    ‖contrast W p Y z‖≤‖contrast W p Y x‖+K*‖x-z‖:=by
  let κ:=WilsonMacroscopicRichSingleWatch.target (S:=S) W h
  obtain hk:= (WilsonMacroscopicRichSingleWatch.original F W h).norm.eventually_lt_const (show ‖κ‖<‖κ‖+1 by linarith)
  refine ⟨‖κ‖+1,by positivity,?_⟩;filter_upwards [hk] with p mp Y x z
  have diff:contrast W p Y z=contrast W p Y x+row W h p (x-z):=by
    unfold contrast row;rw [LinearMap.comp_apply];simp only [map_sub];ring
  rw [diff];apply (norm_add_le _ _).trans;apply add_le_add le_rfl
  exact ((row W h p).toContinuousLinearMap.le_opNorm (x-z)).trans (mul_le_mul_of_nonneg_right mp.le (norm_nonneg _))

end YM.Integration.WilsonSeparatedOriginalSlabWatchTransfer
