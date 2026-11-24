import YM.Integration.FVA1Physical.Marked.CurrentRunSpatial
import YM.MSbar.RawP.Flank

/-! The countable regular bank paid by the actual marked representation in
ordinary exponential-field coordinates. Each derivative slot consumes its
own distance to the distinguished source. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Push Push.Uniform
open MSbar MSbar.Measuring MSbar.Lis MSbar.Midpoint MSbar.RawP MSbar.Wave MSbar.Rolling
open AnalyticBridge.SectorAffine.Offset PhysicalNext.Repeat Push.AbsoluteSums
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side} {p:BudgetPoint}
local notation "E" => Positions (Primary n G)

/-- The rooted location weight holds for the actual chart's ordinary derivatives
of the summed regular bank. The bank can be countably infinite. -/
theorem chart_bank {ι:Type} {o:Site n} {S:ι → Support n} {f:ι → Config G n → ℝ}
    {a:ι → ℝ} {C α:ℝ} (regular:∀ i,p.Regular (S i) (f i))
    (bills:∀ i,p.supBounds o (S i) (f i) (a i)) (root:∀ i,o∈S i)
    (credit:SumBudget (fun i=>p.mass (S i) (a i)) C)
    {k:ℕ} (order:k≤p.order) (α0:0≤α)
    (room:α*k*(6*p.B+2:ℝ)≤p.supportExponent) {x:E} (small:‖x‖<1)
    (clear:palace x∈Boulevard.sunny p) :
    ContDiffAt ℝ k (fun z=>∑' i,Program (f i) z) x ∧
    Beacon (Measuring.chart n G) α k (fun z=>∑' i,Program (f i) z) o x (earnE p G k*C) := by
  let charge:=earnE p G k
  have c0:0≤charge:=floorP G p k
  have hc:Continuous (palace (G:=G) (c:=n)) := by
    apply continuous_pi
    intro e
    exact (G.lieExp_cont.comp ((continuous_apply e).comp (panel G n).continuous)).mul continuous_const
  have near : ∀ᶠ z in 𝓝 x,‖z‖<1 ∧ palace z∈Boulevard.sunny p :=
    (continuous_norm.continuousAt.eventually_lt continuousAt_const small).and
      (hc.continuousAt.eventually ((Boulevard.sky p).mem_nhds clear))
  obtain ⟨δ,δ0,valid⟩:=Metric.eventually_nhds_iff.mp near
  let ball:=Metric.ball x δ
  have good (z:E) (hz:z∈ball) : ‖z‖<1 ∧ palace z∈Boulevard.sunny p:=valid (Metric.mem_ball.mp hz)
  have norm (i:ι) (z:E) (hz:z∈ball) : Through k (Program (f i)) z (charge*a i) :=
    fluxP (d:=⟨o,S i,root i⟩) (regular i) (bills i) (by unfold Healthy;rw [Boulevard.smoky (good z hz).2];simp)
      order (good z hz).1.le
  have ordinary:=budget_mono credit (fun i=>(bills i).1) (fun i=>p.loMass _ _ (bills i).1)
  have center:x∈ball:=Metric.mem_ball_self δ0
  have summable:Summable (fun i=>charge*a i):=ordinary.2.1.mul_left charge
  have hp:=topS (f:=fun i=>Program (f i)) Metric.isOpen_ball (convex_ball x δ) norm summable x center
  refine ⟨hp.smooth,?_⟩
  let v:=fun i=>charge*p.mass (S i) (a i)
  have one (i:ι) : Beacon (Measuring.chart n G) α k (Program (f i)) o x (v i) := by
    let radius:=(6*p.B+2)*coverNumber p.B (S i)
    have tied: Requests Set.univ (Program (f i)) (Measuring.chart n G) o radius := by
      intro u _ w _ equal
      apply (regular i).sites
      intro e hinside _
      apply Eq.trans (Work.F03.represent_link ((tint G _) u) e)
      refine Eq.trans (congr_arg G.lieExp (?_: tint G _ u (e.1,Exterior.coord e.2)=
        tint G _ w (e.1,Exterior.coord e.2))) (Work.F03.represent_link ((tint G _) w) e).symm
      ext j
      apply equal
      change separation o e.1 ≤ radius
      unfold radius
      have nc:= (Animals.price_pos p.B (S i)).2 ⟨o,root i⟩
      nlinarith only [Corona.extent (S i) p.B (root i) hinside,Nat.mul_le_mul_left (2*p.B) nc]
    have dr : charge*a i*Real.exp (α*(k*radius:ℕ)) ≤ v i := by
      have exponent : α*(k*radius:ℕ) ≤ p.supportExponent*coverNumber p.B (S i) := by
        unfold radius
        push_cast
        exact (mul_le_mul_of_nonneg_right room (Nat.cast_nonneg (α:=ℝ) (coverNumber p.B (S i)))).trans_eq' (by ring)
      unfold v BudgetPoint.mass
      calc
        _ ≤ charge*a i*Real.exp (p.supportExponent*coverNumber p.B (S i)) :=
          mul_le_mul_of_nonneg_left (Real.exp_monotone exponent) (mul_nonneg c0 (bills i).1)
        _ = _ := by ring
    intro j hj q
    exact (riseA (norm i x center) tied α0 j hj q).trans (mul_le_mul_of_nonneg_right dr (Real.exp_pos _).le)
  have joined := cargo (g:=fun i=>Program (f i)) (t:=fun i=>charge*a i) (v:=v)
    Metric.isOpen_ball (convex_ball x δ) norm center summable (credit.2.1.mul_left charge) one
  intro j hj q
  apply (joined j hj q).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  simpa only [v,tsum_mul_left] using mul_le_mul_of_nonneg_left credit.2.2 c0
end YM.Integration.FVA1Physical.Marked
