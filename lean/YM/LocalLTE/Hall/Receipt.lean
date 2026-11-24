import YM.LocalLTE.Hall.Trim
/-! Numerical log fits at scale P. Don't use for wrap/no stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide Grove
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (L : Side) (j p i:ℕ) {κ v w t t' e q:ℝ} {g d:ℝ→ℝ} {n:ℝ→ℕ}
include j i
lemma prunes (hn: Rate G L 0 fun t=>(n t:ℝ)) (hR: Reliable G κ t) (hv: -(7/16:ℝ)≤v) (hw:v<0) (hg:Rate G L t' g) (hf:t'+v*i < e):
    ∀ᶠ x in atTop,∀ P:BudgetPoint,P.power=p → P.order=j → P.threshold=Pressure.temp x → P.threshold≤2*Pressure.fiery G x L → ∀ N m:ℕ, N ≤ n x→m+1≤ N →∀ (c:Side)(o:Site c)(_ :2*N<c.val)(_ :2*(2*m)≤c.val)(X:Grove o)(f:Config G c→ℝ), P.Regular (neighbors m o) f → ∀ C:ℝ,0≤C →(∀ u:Directions G c,‖u‖ < cone v (betaF G x L) → Brush (i+j) (C*g x) 1 (f ∘ soloV) u) → P.supBounds o (neighbors N o) (f-shave X m κ i f) (C*(betaF G x L)^e) := by
      let w := (-(15/32:ℝ)); have hw₁:w<v:=by unfold w; linarith only [hv]
      obtain ⟨E,hE,hX⟩:= minted G L hn hR hw₁ hw (by unfold w; norm_num) (by unfold w vow; norm_num) j p
      have hr: Rate G L (0+(t'+v*(i:ℝ))) (fun x=>E x*(g x*cone v (betaF G x L)^i)):= hE.mul (hg.mul (Rate.power.pow i))
      filter_upwards [Delay.shift_pos G L, hX, hr e (by linarith), Sienna.contraction G L (a:=1) (b:=1) zero_lt_one (Rate.power (a:=v)) hw] with x h hy hx hc P hp hP ht ht' N m hN hm c o hz' hh X f hF C hC hu
      let d:= cone v (betaF G x L); have hv':0<d:=Real.rpow_pos_of_pos h _; rw [one_mul,Real.rpow_zero,one_mul] at hc
      have hg':0 ≤C*g x:= (hu 0 (by rw [norm_zero]; exact hv')).nonneg
      let w:= C*g x*d^i; have hw : 0≤w:=mul_nonneg hg' (pow_nonneg hv'.le _)
      have hK := hy _ _ hN hm P hp hP ht ht' _ o hz' hh X i (bushes i f) f w hw hF (?_); swap
      · intro u hv hm; rw [bays]; let hV (u:Directions G c)(he:u∈ Metric.ball 0 d):= hu u (mem_ball_zero_iff.mp he)
        exact (LocalLTE.pays hv' hc.le hg' (show i ≤ i+j from Nat.le_add_right ..) (fun z hz=> (hV z hz).smooth) (fun z hz k _ hk=>(Brush.offer.mp (hV z hz)).2 _ hk) u (mem_ball_zero_iff.mpr hv)).smaller (show j ≤ i+j from by omega)
      refine AnalyticBridge.VerifiedReset.sup_le hK (?_)
      exact (show E x * w=C * (E x*(g x*d^i)) by unfold w; ring).trans_le (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hx) hC)
end YM.LocalLTE.FrameBox.Hall
