import YM.OPE.Compatible.Jess.Soft
/-! # Thermal pedal. limits of differentiable columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
variable {K:Sponsor G}{T:Seasons K}{v u b:ℝ}
local notation "Lf"=> Tested.germ
lemma refresh (p:ℕ→ℝ→ℝ)(q:ℝ→ℝ)(hp:∀ i,Bond (p i))(hq:Bond q)(K:ℕ)(h:∀ i,∃ v:ℝ,0≤v∧∀ x:ℝ, ‖p i x-q x‖≤ v*(1+‖x‖)^K)(ht:∀ x,Tendsto (fun i=> p i x) atTop (𝓝 (q x)))(x:ℝ):Tendsto (fun i=>deriv (p i) x) atTop (𝓝 (deriv q x)):=by
     let V(t:ℝ):=x+t; have hx:Gael V:= Exists.intro _ ((Reads.constants x).sum Arc.readsId); let y(i):=p i-q; have hh(i):Bond (y i):=(hp i).sub hq; have hg(v:ℝ):Tendsto (fun i=>y i v) atTop (𝓝 0) :=by simpa only [sub_self] using! (ht v).sub_const (q v)
     have hy:= Essay.pears (ContinuousLinearMap.id ℝ ℝ) y hh K h hg V hx 1; apply tendsto_sub_nhds_zero_iff.mp
     have he(f:ℝ→ℝ)(hv: Bond f): (trill (f∘V)).seq (1:Phase).val= deriv f x:=by
          let g:=f∘V; have hV:ContDiff ℝ ∞ V:=contDiff_const.add contDiff_id; have hp:= Pawn.calm ( (hv.smooth.of_le le_top).comp hV|>.contDiffAt (x:=(0:ℝ))); rw [show trill _= _ from (show trill (f∘V)= _ from (Gael.chooses ((hp.stale (1:ℝ)).cong (by filter_upwards with i; simp only [smul_eq_mul,mul_one]))))]; change jet _ 1 1= _; unfold jet;rw [iteratedFDeriv_one_apply]; simp only [Nat.factorial_one,Nat.cast_one,inv_one,one_mul]; rw [fderiv_apply_one_eq_deriv,deriv_comp]; rotate_left -- name check
          · exact hv.smooth.differentiable (by simp) _
          · exact hV.differentiable (by simp) _
          have he:HasDerivAt V 1 0:=(hasDerivAt_id' _).const_add x; rw [he.deriv,mul_one,show V 0=x from add_zero _]
     simp_rw [he _ (hh _)] at hy; have hz(i):deriv (y i) x=deriv (p i) x-deriv q x:=deriv_sub ((hp i).smooth.differentiable (by simp) _) (hq.smooth.differentiable (by simp) _); simp_rw [hz] at hy; exact hy
