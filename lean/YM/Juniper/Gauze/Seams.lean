import YM.Juniper.Gauze.Port
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld

/-! # Continuation and bracketing
   Seam issue: old RISING asks too large an envelope to get arctic cost
   for the traveler at radius eaves (period growing). Generalize its volatile
   exponent (closer to -1/2 than β-vow); use AFTER higher cut on H and Ξ
   behind extra slim gains. `risingFlex,pledgesFlex` adapt the proof of
   `Boulevard.rising`, `Trio.pledges` from Views/Weld: re-pay geometry
   and small interior invocation AFTER choosing flex. Keep brush-scaled
   expenses WITH THAT exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Gauze
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel PhysicalNext PhysicalNext.Repeat Boulevard Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X t : ℝ} {f : Config G c→ℝ}
section seam
variable (G L) (lp:ℝ)(hLaw: -(1/2:ℝ) < lp)(hLawr: lp < -(1/4:ℝ))
local notation "p'" => (fun x=> (betaF G x L)^ lp)
local notation "d'" => furl G L
include hLaw hLawr
lemma risingFlex (j : ℕ) : ∀ᶠ x in atTop,∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=j →
    ∀ (c:Side) (W:Positions (Uniform.Primary c G)), ‖W‖+2*d' x < p' x →
      flags P.threshold (actual W)=∅ → ∀ (S:ℕ→RegularAddress c) (u:ℕ→ Config G c→ℝ) (H f:Config G c→ℝ)
    (v b z:ℝ), Meadow.Budget P S u b→P.Regular univ H → (∀ V∈ sunny P,f V=z-H V-Boulevard.throng u V) →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*d' x < p' x → actual W'∈ sunny P→ Brush j v (p' x)⁻¹ ((Boulevard.stillA f)∘actual) W') →
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs (Boulevard.stillA H) l (actual W)‖ ≤ ticket j v + 2*((Fintype.card (Site c):ℝ)*b):= by
  obtain ⟨s,hs,he⟩:= oar G j
  obtain ⟨J,d,hS⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hc,hQ⟩:= seek (G:=G) hS.pos
  obtain ⟨p,h,hp⟩:= expCost G 2 1
  let u t:= s*(2*Pressure.fiery G t L); let t x:=(1+ (j:ℝ))* u x; let r:= royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
  have hR : Rate G L (-(1/2)) (fun x=>(1+r)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let w x:= Uniform.shade G* p' x
  have hw: Rate G L lp w:= Rate.power.mul_left _
  let g x:=4*(sunLength p (w x) * r)
  have hg : Rate G L lp g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw (show lp <0 from by linarith only [hLawr]) hc,hw.below (show lp <0 from by linarith only [hLawr]) 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=lp*2) (hg.pow 2) (show lp*2 < -(1/2:ℝ) by linarith only [hLawr]), softly G L, hR.below (by norm_num) 1 zero_lt_one,
    Sienna.contraction G L (a:= j.factorial*J) zero_lt_one hR (show -(1/2:ℝ)<lp from hLaw)] with
    x hx hx' hw hX hZ hv he' P ht hb hP c W hW hh S u' H f v b z hB h' hT hF l hl hL
  have hC:0<u x:= mul_pos hs (P.threshold_pos.trans_le hb); have hf : 0< t x:= by unfold t; positivity
  have hz:0< p' x:=Real.rpow_pos_of_pos hx _; have hd:0<d' x:=Real.rpow_pos_of_pos hx _
  have hℓ : 0≤j:=Nat.zero_le _
  have hΩ : ‖W‖< p' x:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_pos (by norm_num) hd).le) hW
  let Q (k:ℝ):=actual (k • W)
  have he'' := sunnySoon p (w x) hp W (mul_le_mul_of_nonneg_left hΩ.le (Uniform.shade_pos G).le) ((le_abs_self _).trans hw) hh (by
    change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hx.le]; exact hZ.2)
  have hhP : P.Regular univ (stillA H):= CouplingShape.reg_sub h' (CouplingShape.reg_const _)
  have h0: Push.Local.Chart P.order (stillA H) (Q 1):= hhP.smooth _ (by unfold Healthy Q; rw [one_smul,hh]; simp)
  have h1:Push.Local.Chart 0 (leftDerivs (stillA H) l) (Q 1) := Next.Foundations.leftDerivs_chart _ _ (h0.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl)) -- edit
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
  exact tightens (V:=Q i) hi hB hT (hP.symm ▸ hp.1) (fun l hl=> hp.2 l (hl.trans_eq (by exact hP))) l hl hL
end seam

open Slide
section flatten
lemma pledgesFlex (lp:ℝ)(hLaw:-(1/2:ℝ)<lp) (G: Gauge) (L: Side) (Y:ℝ→ℕ) (h: Rate G L 0 fun x=>(Y x:ℝ)): ∀ᶠ x in atTop, ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2* Y x<c.val→∀ w:ℕ,w+1≤Y x→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors (Y x) o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < (betaF G x L)^lp:= by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let f x:= 16*(2*(Y x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hv : Rate G L (-(1/2)) f:= by
    simpa only [f,zero_mul,zero_add] using! (((((h.mul_left 2|>.add (Rate.const 1)).pow 5).mul_left _).mul_right _).mul ((Rate.flame (G:=G) (L:=L)).mul_left 2))
  filter_upwards [hv.below (by norm_num) d hd, contraction G L (a:=1) (b:=1) zero_lt_one ((hv.mul_left A).add ((Sienna.belt G L|>.mul_left 2).weaken (by norm_num))) (show -(1/2:ℝ)<lp from hLaw)] with x hv hK P hx c g h w hp u o V he
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
end YM.Juniper.Gauze
