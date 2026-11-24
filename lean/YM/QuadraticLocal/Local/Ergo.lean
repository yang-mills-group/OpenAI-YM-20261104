import YM.AllOrder.Horizon.Dust
import YM.RemainderComparison.Portal.Count
/-! # Tally hiring at ANY low descriptor. No off and MASS includes origin. This
 implements analogous clock demands from Moon.Clock.rising_slender under markup.Book.Grid.
 Tall topology for all tail stanzas and marked rotor measure.Meta. Adapted from
 YM/AllOrder/Horizon/Dust.lean, YM/RemainderComparison/Portal/Cup.lean -/
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
variable (G L) {η : ℝ}
local notation "p'" => (fun x=> betaF G x L ^ η)
local notation "d'" => furl G L
namespace Mark
open RemainderComparison.Portal
variable {b:ℝ}
lemma branch {f H:Config G c→ℝ}{κ:Type}{W:κ→ Config G c→ℝ}(h:Tally P κ W b)(he:∀ V∈ sunny P,f V= H V+unite W V) (U:Config G c)(hu:U∈sunny P)
   (hh:Push.Local.Chart P.order f U) (hf:∀ l:List (Directions G c), l.length≤P.order→ (∀ i ∈l,‖i‖≤P.threshold) → ‖leftDerivs f l U‖ ≤y) :
    ∀ l:List (Directions G c), l.length≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs H l U‖ ≤ y+b:= by
 let t:= unite W; have ht:H=ᶠ[𝓝 U] f-t:= by filter_upwards [(sky P).mem_nhds hu] with i hi; change H i=f i-t i; rw [he i hi]; unfold t; abel
 intro l hl h'; obtain ⟨-,hz,hD⟩:=levy h U hu; rw [(UVNext.PricedKernels.left_congr ht l).self_of_nhds,VerifiedReset.left_sub hh (show Push.Local.Chart P.order t U from hz) hl]; exact (norm_sub_le ..).trans (add_le_add (hf l hl h') (hD l hl h'))
lemma rich (h0 : -(1/2:ℝ)<η) (hU : η*2< -(1/2:ℝ)) (j : ℕ) : ∀ᶠ x in atTop,∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=j →
    ∀ (c:Side) (W:Positions (Uniform.Primary c G)), ‖W‖+2*d' x < p' x →
      flags P.threshold (actual W)=∅ → ∀ (S:Type) (u:S→ Config G c→ℝ) (H f:Config G c→ℝ)
    (v b:ℝ), Tally P S u b→P.Regular univ H → (∀ V∈ sunny P,f V=H V+unite u V) →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*d' x < p' x → actual W'∈ sunny P→ Brush j v (p' x)⁻¹ (f∘actual) W') →
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs H l (actual W)‖ ≤ ticket j v+b:= by
  obtain ⟨s,hs,he⟩:= oar G j
  obtain ⟨J,d,hS⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hc,hQ⟩:= seek (G:=G) hS.pos
  obtain ⟨p,h,hp⟩:= expCost G 2 1
  let u t:= s*(2*Pressure.fiery G t L); let t x:=(1+ (j:ℝ))* u x; let r:= royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
  have hR : Rate G L (-(1/2)) (fun x=>(1+r)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let w x:= Uniform.shade G* p' x
  have hw: Rate G L η w:= (Rate.power (a:=η) (G:=G) (L:=L)).mul_left _
  let g x:=4*(sunLength p (w x) * r)
  have hg : Rate G L η g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw (show η<0 by linarith only [hU]) hc,hw.below (show η<0 by linarith only [hU]) 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=η*2) (hg.pow 2) hU, softly G L, hR.below (by norm_num) 1 zero_lt_one,
    Sienna.contraction G L (a:= j.factorial*J) zero_lt_one hR h0] with
    x hx hx' hw hX hZ hv he' P ht hb hP c W hW hh S u' H f v b hB h' hT hF l hl hL
  have hC:0<u x:= mul_pos hs (P.threshold_pos.trans_le hb); have hf : 0< t x:= by unfold t; positivity
  have hz:0< p' x:=Real.rpow_pos_of_pos hx _; have hd:0<d' x:=Real.rpow_pos_of_pos hx _
  have hℓ : 0≤j:=Nat.zero_le _
  have hΩ : ‖W‖< p' x:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_pos (by norm_num) hd).le) hW
  let Q (k:ℝ):=actual (k • W)
  have he'' := sunnySoon p (w x) hp W (mul_le_mul_of_nonneg_left hΩ.le (Uniform.shade_pos G).le) ((le_abs_self _).trans hw) hh (by
    change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hx.le]; exact hZ.2)
  have hhP : P.Regular univ H:= h'
  have h0: Push.Local.Chart P.order H (Q 1):= hhP.smooth _ (by unfold Healthy Q; rw [one_smul,hh]; simp)
  have h1:Push.Local.Chart 0 (leftDerivs H l) (Q 1) := Next.Foundations.leftDerivs_chart _ _ (h0.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl)) -- edit
  have hY := (Push.Local.chart_comp h1 (fun i=> radiator 1 W i)).continuousAt.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  let U k:= f k
  rw [show actual W = Q 1 from by simp [Q] ]
  apply le_of_tendsto hY
  filter_upwards [he'', self_mem_nhdsWithin (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with i hi hk hp'
  let x':=i • W; have hk: ‖x'‖≤ ‖W‖:= by rw [show x'=i • W from rfl,norm_smul,Real.norm_of_nonneg hp']; exact mul_le_of_le_one_left (norm_nonneg _) (show i≤1 from le_of_lt hk)
  have hH:= hF x' (lt_of_le_of_lt (add_le_add hk le_rfl) hW) hi
  have hp:= hires (x:=x') hS (fun a hh=>hQ a (hh.trans hx'.le)) hz (hk.trans hΩ.le) hH (show j.factorial*J*((1+r)* t x)≤ p' x from le_of_lt (by rw [one_mul] at he'; exact he')) ((le_abs_self _).trans hv)
    (show Sailor G P.threshold (u x) j from ⟨fun c a hv=> he c _ (P.threshold_pos.trans_le hb).le a (hv.trans hb)⟩) hC hf
    (show (j:ℝ)*(u x) ≤ t x from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC.le)
  exact branch G hB hT (Q i) hi (hP.symm ▸ hp.1) (fun l hl=> hp.2 l (hl.trans_eq (by exact hP))) l hl hL
end Mark
end seam
end YM.PhysicalNext.Repeat.Boulevard
