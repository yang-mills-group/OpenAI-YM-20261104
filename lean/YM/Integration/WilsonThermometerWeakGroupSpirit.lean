import YM.Integration.WilsonThermometerWeakGroupCoupon

/-! Nonlinear gauge invariance of the actual filed group word. The unmasked
Taylor series is extracted from its genuine gauge-invariant Wilson occurrences. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGroupSpirit
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer Atlas Tariffs MvPolynomial Ribbon Asymptotics
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {n:Side} {D b:ℕ} {P:BudgetPoint} {S:Rules G}
variable {ι:Type*} {X:ι→Support n} {A:ι → Config G n → ℂ} {f:ι→ℂ}
variable {rent cash:ℝ} {L:poly (links G (0:Site n) b)}

private def logRay (p:BudgetPoint) (z:Space G (0:Site n) b) (A:ι → Config G n → ℂ) (f:ι→ℂ)
    (t:ℝ):ℂ:=∑' i,f i*A i (monitor G p z t)

private theorem remainder (h:Summary S P b D X A f rent cash L) (x:Space G (0:Site n) b) :
    asym D (logRay P x A f-seen L x) := by
  obtain ⟨e,ce,T⟩:=h
  have slim:Tendsto (fun t:ℝ=>t•x) (𝓝 0) (𝓝 0):=by simpa using!
    (continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)
  apply error_power (cash*‖x‖^(D+1))
  filter_upwards [slim.eventually (Metric.ball_mem_nhds (0:Space G (0:Site n) b) (pane_pos S))] with t ht
  rw [dist_zero_right] at ht
  have h:=((T.calls (t•x) ht.le).2).trans (mul_le_mul_of_nonneg_right ce.2.2 (pow_nonneg (norm_nonneg _) _))
  apply h.trans_eq;rw [norm_smul];ring

theorem represented (H:Summary S P b D X A f rent cash L) (x:Space G (0:Site n) b) (u:G.El) :
    text (scan (coloring u x)) L=text (scan x) L := by
  let y:=coloring u x
  have same (t:ℝ):logRay P x A f t=logRay P y A f t := by
    have h:monitor G P y t=Lattice.gauge (fun _=>u) (monitor G P x t):=by
      unfold monitor y;rw [←land_smul];exact land_eq ..
    unfold logRay;rw [h];apply tsum_congr;intro i
    exact congrArg (f i*·) ((H.choose_spec.2.smooth i).symmetry (fun _=>u) _).symm
  have price:asym D (seen L y-seen L x) := by
    apply ((remainder H x).sub (remainder H y)).congr_left
    intro t;change (logRay P x A f t-seen L x t)-(logRay P y A f t-seen L y t)=seen L y t-seen L x t;rw [same];ring
  have deg:=H.choose_spec.2.produced.choose_spec.1.degree
  have h:=congrFun (decipher D (seen L y) (seen L x) (verse _ _ _ deg) (verse _ _ _ deg) price) 1
  simpa only [Spindle.seen,one_smul] using h

theorem field (live:2*(b+1)<n.val) (t g:ℝ)
    (h:∀ x:Space G (0:Site n) b,∀ u:G.El,text (scan (coloring u x)) L=text (scan x) L):
    Spirit (sender live t g L) := by
  intro x u
  have read (z:Turn b→G.Color):
      text (fun i:slotC G b=>z i.1 i.2) (sender live t g L)=text (scan (rows 1 live ((g/t)•z))) L := by
    apply (sold_factor (g/t) (fun i:slotC G b=>z i.1 i.2) (dustAt live L)).trans
    exact full_dust live ((g/t)•z) L
  rw [read,read,show (g/t)•coloring u x=coloring u ((g/t)•x) from
      funext fun j=>(G.adjoint u |>.map_smul (g/t) (x j)).symm,tinted]
  exact (h _ _).symm

end YM.Integration.WilsonThermometerWeakGroupSpirit
end
