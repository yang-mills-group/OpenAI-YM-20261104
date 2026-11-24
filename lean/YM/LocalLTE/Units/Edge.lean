import YM.LocalLTE.Frame.Edge
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Ebb
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts
import YM.LocalLTE.Frame.Prices
/-! Adaptation of Boulevard.Views for general power-window repair -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X t : ℝ} {f : Config G c→ℝ}
section seam
variable (G L)
variable {w:ℝ} (hp₁: -(1/2:ℝ)<w) (hp₂:w<vow)
include hp₁ hp₂
local notation "p'" => (fun x=> YM.LocalLTE.Inset.cone w (betaF G x L))
local notation "d'" => furl G L
lemma equalityG (j : ℕ) : ∀ᶠ x in atTop,∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=j →
    ∀ (c:Side) (W:Positions (Uniform.Primary c G)), ‖W‖+2*d' x < p' x →
      flags P.threshold (actual W)=∅ → ∀ (Z:Finset (Site c))(f: Config G c→ℝ) (v:ℝ), P.Regular Z f →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*d' x < p' x → actual W'∈ sunny P→ Brush j v (p' x)⁻¹ (f∘actual) W') → ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs f l (actual W)‖ ≤ ticket j v:= by
  obtain ⟨s,hs,he⟩:= oar G j
  obtain ⟨J,d,hS⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hc,hQ⟩:= seek (G:=G) hS.pos
  obtain ⟨p,h,hp⟩:= expCost G 2 1
  let u t:= s*(2*Pressure.fiery G t L); let t x:=(1+ (j:ℝ))* u x; let r:= royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
  have hR : Rate G L (-(1/2)) (fun x=>(1+r)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let wX x:= Uniform.shade G* p' x
  have hw: Rate G L w wX:= (Rate.power (G:=G) (L:=L) (a:=w)).mul_left _
  let g x:=4*(sunLength p (wX x) * r)
  have hg : Rate G L w g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw (hp₂.trans vow_ok) hc,hw.below (hp₂.trans vow_ok) 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=w*2) (hg.pow 2) (show w*2 < -(1/2:ℝ) by unfold vow at hp₂; linarith), softly G L, hR.below (by norm_num) 1 zero_lt_one,
    Sienna.contraction G L (a:= j.factorial*J) zero_lt_one hR hp₁] with
    x hx hx' hw hX hZ hv he' P ht hb hP c W hW hh Z f v h' hF l hl hL
  have hC:0<u x:= mul_pos hs (P.threshold_pos.trans_le hb); have hf : 0< t x:= by unfold t; positivity
  have hz:0< p' x:=Real.rpow_pos_of_pos hx _; have hd:0<d' x:=Real.rpow_pos_of_pos hx _
  have hℓ : 0≤j:=Nat.zero_le _
  have hΩ : ‖W‖< p' x:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_pos (by norm_num) hd).le) hW
  let Q (k:ℝ):=actual (k • W)
  have he'' := sunnySoon p (wX x) hp W (mul_le_mul_of_nonneg_left hΩ.le (Uniform.shade_pos G).le) ((le_abs_self _).trans hw) hh (by
    change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hx.le]; exact hZ.2)
  have h0: Push.Local.Chart P.order f (Q 1):= h'.smooth _ (by unfold Healthy Q; rw [one_smul,hh]; simp)
  have h1:Push.Local.Chart 0 (leftDerivs f l) (Q 1) := Next.Foundations.leftDerivs_chart _ _ (h0.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl)) -- edit
  have hY := (Push.Local.chart_comp h1 (fun i=> radiator 1 W i)).continuousAt.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  let U k:= (Boulevard.stillA f) k
  rw [show actual W = Q 1 from by simp [Q] ]
  apply le_of_tendsto hY
  filter_upwards [he'', self_mem_nhdsWithin (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with i hi hk hp'
  let x':=i • W; have hk: ‖x'‖≤ ‖W‖:= by rw [show x'=i • W from rfl,norm_smul,Real.norm_of_nonneg hp']; exact mul_le_of_le_one_left (norm_nonneg _) (show i≤1 from le_of_lt hk)
  have hH:= hF x' (lt_of_le_of_lt (add_le_add hk le_rfl) hW) hi
  have hp:= hires (x:=x') hS (fun a hh=>hQ a (hh.trans hx'.le)) hz (hk.trans hΩ.le) hH (show j.factorial*J*((1+r)* t x)≤ p' x from le_of_lt (by rw [one_mul] at he'; exact he')) ((le_abs_self _).trans hv)
    (show Sailor G P.threshold (u x) j from ⟨fun c a hv=> he c _ (P.threshold_pos.trans_le hb).le a (hv.trans hb)⟩) hC hf
    (show (j:ℝ)*(u x) ≤ t x from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC.le)
  exact hp.2 l (hl.trans_eq hP) hL
end seam
end YM.PhysicalNext.Repeat.Boulevard
