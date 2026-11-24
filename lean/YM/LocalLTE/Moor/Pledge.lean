import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Mover
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Panel
import YM.LocalLTE.Frame.Payment
/-! Pledge into expanded AUX comparing torus. Tied to actual Gas balance. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side} {q : ℝ}
section flatten
lemma summoned (G: Gauge) (L: Side) (v:ℝ) (hW : -(1/2:ℝ)<v) (Y:ℝ→ℕ) (h: Rate G L 0 fun x=>(Y x:ℝ)): ∀ᶠ x in atTop, ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2* Y x<c.val→∀ w:ℕ,w+1≤Y x→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors (Y x) o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < YM.LocalLTE.Inset.cone v (betaF G x L):= by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let f x:= 16*(2*(Y x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hv : Rate G L (-(1/2)) f:= by
    simpa only [f,zero_mul,zero_add] using! (((((h.mul_left 2|>.add (Rate.const 1)).pow 5).mul_left _).mul_right _).mul ((Rate.flame (G:=G) (L:=L)).mul_left 2))
  filter_upwards [hv.below (by norm_num) d hd, contraction G L (a:=1) (b:=1) zero_lt_one ((hv.mul_left A).add ((Sienna.belt G L|>.mul_left 2).weaken (by norm_num))) hW] with x hv hK P hx c g h w hp u o V he
  have hf :0≤ f x:= by have hh := P.threshold_pos.trans_le hx; unfold f; positivity
  have hj (y:Site c) (hy:separation o y≤Y x) (p : PlaqAxes): toll V (y,p) ≤ P.threshold:= by by_contra! hv; exact Finset.disjoint_left.mp he ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p),WilsonStartup.anchor_visit _,hv⟩)
  obtain ⟨a,ha⟩:= Work.E08.axial_patch o V w (Y x) hp h (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hx).le (fun y hy p=> (hj y hy p).trans hx)
  · let z (i:Site g):= a (Slide.sites (Slide.cognac u) o i); let g':=Slide.shape (Slide.cognac u) o V
    let W:= gauge z g'; have he i:G.chord (W i) ≤ f x:= by
      unfold W g'; rw [show gauge z (Slide.shape (Slide.cognac u) o V)=_ from (Slide.shape_gauge (Slide.cognac u) o a V).symm]; unfold Slide.shape; split; exact ha _ (Slide.village ..)
      split; next h'=> rw [G.chord_inv]; exact ha _ (Slide.village ..)
      simpa [Gauge.chord] using hf
    obtain ⟨b,hb,hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (f x) hf ((le_abs_self _).trans hv) (fun i _=>he i)
    refine ⟨z,(Uniform.tint G _).symm b,?_,lt_of_le_of_lt (add_le_add ((Uniform.tint_inv_le _).trans hb) le_rfl) (by simpa only [one_mul] using! hK)⟩
    unfold Boulevard.actual; rw [ContinuousLinearEquiv.apply_symm_apply]; exact funext fun i=> (hQ i (by simp)).symm
end flatten
end YM.PhysicalNext.Repeat.Trio
