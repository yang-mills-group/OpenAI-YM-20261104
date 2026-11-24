import YM.RGComparison01.Pencils
/-!
# Safe radius scaling

 Real scale survives on a radius `g * polynomial in monitor`, not L-fixed.
 Push from sunny to *closed* flag-passing points there using genuine
 boundary estimate from Boulevard, reproduce its seam argument at this
 smaller radius. Pays all angular/axial apertures.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sluice
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open RG.Supply RG.Shoot Push.Uniform Sienna Fare Lapis Metric Further.LogJets Blaze.Frond
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G : Gauge) (L : Side) (j b : ℕ)
local notation "p'" => eaves G L
local notation "d'" => furl G L
local notation "M" => Pressure.betaF G

/-- A usable boundary inequality when near points use lease density. -/
def Shore (t r : ℝ) := ∀ P:BudgetPoint,P.order=j → P.threshold=Pressure.temp t → P.threshold ≤ 2*Pressure.fiery G t L →
    ∀ {c:Side},∀ (W:Positions (Uniform.Primary c G)), ‖W‖+2*d' t < r →
      flags P.threshold (actual W)=∅ → ∀ (S:ℕ→RegularAddress c) (u:ℕ→ Config G c→ℝ) (H f:Config G c→ℝ)
    (v b z:ℝ), Meadow.Budget P S u b→ P.Regular univ H → (∀ V∈ sunny P,f V=z-H V-Boulevard.throng u V) →
      (∀ W': Positions (Uniform.Primary c G),‖W'‖+2*d' t < r → actual W'∈ sunny P→ Brush j v r⁻¹ ((Boulevard.stillA f)∘actual) W') →
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l,‖i‖≤P.threshold) → ‖leftDerivs (Boulevard.stillA H) l (actual W)‖ ≤ ticket j v + 2*((Fintype.card (Site c):ℝ)*b)
lemma parcel : ∃ C:ℝ, ∀ᶠ t:ℝ in atTop, ∀ r, 0<r → C*Pressure.fiery G t L ≤ r → r≤p' t → Shore G L j t r := by
  obtain ⟨s,hs,he⟩:= oar G j
  obtain ⟨J,d,hS⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hc,hQ⟩:= Boulevard.seek (G:=G) hS.pos
  obtain ⟨p,h,hp⟩:= expCost G 2 1
  let u t:= s*(2*Pressure.fiery G t L); let t x:=(1+(j:ℝ))*u x; let r:= royalty G; have hr:0<r:= zero_lt_one.trans_le (royalty_ge G)
  have hR : Rate G L (-(1/2)) (fun x=>(1+r)*t x):= ((((Rate.flame (G:=G) (L:=L)).mul_left _).mul_left _).mul_left _).mul_left _
  let w x:= Uniform.shade G* p' x
  have hw: Rate G L vow w:= (Sienna.edge G L).mul_left _
  let g x:=4*(sunLength p (w x) * r)
  have hg : Rate G L vow g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  let v:ℝ:= j.factorial*J*(1+r)*(1+j)*s*2
  refine ⟨v,?_⟩
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw vow_ok hc,hw.below vow_ok 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=vow*2) (hg.pow 2) (show vow*2 < -(1/2:ℝ) by norm_num [vow]), softly G L, hR.below (by norm_num) 1 zero_lt_one] with x hx hx' hw hX hZ hv R hRp hi' hY P hP ht hb c W hW hh S u' H f B b z hB h' hT hF l hl hL
  have hC:0<u x:= mul_pos hs (P.threshold_pos.trans_le hb); have hf : 0< t x:= by unfold t; positivity
  have hd:0<d' x:=Real.rpow_pos_of_pos hx _
  have hΩ : ‖W‖< R:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_pos (by norm_num) hd).le) hW
  let Q (k:ℝ):=actual (k • W)
  have he'' := sunnySoon p (w x) hp W (mul_le_mul_of_nonneg_left (hΩ.le.trans hY) (Uniform.shade_pos G).le) ((le_abs_self _).trans hw) hh (by
    change r*(g x)^2<P.threshold*r; refine hX.trans_le ?_; rw [mul_comm r,ht]; apply mul_le_mul_of_nonneg_right _ hr.le; rw [Real.rpow_neg hx.le]; exact hZ.2)
  have hhP : P.Regular univ (stillA H):= CouplingShape.reg_sub h' (CouplingShape.reg_const _)
  have h0: Push.Local.Chart P.order (stillA H) (Q 1):= hhP.smooth _ (by unfold Healthy Q; rw [one_smul,hh]; simp)
  have h1:Push.Local.Chart 0 (leftDerivs (stillA H) l) (Q 1) := Next.Foundations.leftDerivs_chart _ _ (h0.of_le (by simpa using! Nat.cast_le (α:=WithTop ℕ∞)|>.mpr hl))
  have hz := (Push.Local.chart_comp h1 (fun i=> radiator 1 W i)).continuousAt.norm.tendsto.mono_left (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  rw [show actual W = Q 1 from by simp [Q] ]
  apply le_of_tendsto hz
  filter_upwards [he'', self_mem_nhdsWithin (s:=Set.Iio 1), (eventually_ge_nhds (show (0:ℝ)<1 by norm_num)).filter_mono (show (𝓝[<] (1:ℝ)) ≤ 𝓝 1 from nhdsWithin_le_nhds)] with i hi hk hp'
  let x':=i • W; have hk: ‖x'‖≤ ‖W‖:= by rw [show x'=i • W from rfl,norm_smul,Real.norm_of_nonneg hp']; exact mul_le_of_le_one_left (norm_nonneg _) (show i≤1 from le_of_lt hk)
  have hH:= hF x' (lt_of_le_of_lt (add_le_add hk le_rfl) hW) hi
  have hp:= Boulevard.hires (x:=x') hS (fun a hh=>hQ a ((hh.trans (mul_le_mul_of_nonneg_left hY (Uniform.shade_pos G).le)).trans hx'.le)) hRp (hk.trans hΩ.le) hH (show j.factorial*J*((1+r)* t x)≤ R from (le_trans (le_of_eq (show _= v*Pressure.fiery G x L by unfold v t u; ring)) hi')) ((le_abs_self _).trans hv)
    (show Sailor G P.threshold (u x) j from ⟨fun c a hv=> he c _ (P.threshold_pos.trans_le hb).le a (hv.trans hb)⟩) hC hf
    (show (j:ℝ)*(u x) ≤ t x from mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC.le)
  exact tightens (V:=Q i) hi hB hT (hP.symm ▸ hp.1) (fun l hl=> hp.2 l (hl.trans_eq (by exact hP))) l hl hL

def Health (n : ℕ) (t r : ℝ) := ∀ P:BudgetPoint,P.threshold ≤ 2*Pressure.fiery G t L →∀ c f:Side,
    2*n<c.val→∀ w:ℕ,w+1≤n →∀ u:2*w ≤ f.val,∀ (o:Site c) (V:Config G c), Healthy P.threshold (neighbors n o) V → ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)),
      actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*d' t < r

lemma axially (Y:ℝ→ℕ) (h: Geo G L fun x=> (Y x:ℝ)) : ∃ V:ℝ→ℝ, Geo G L V ∧∀ᶠ x in atTop,∀ r, V x*Pressure.fiery G x L < r → Health G L (Y x) x r := by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let g x := 16*(2*(Y x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*2; let f x:= g x*Pressure.fiery G x L
  let V x:= A*g x+1
  have hg: Geo G L g:= ((((Geo.fixed _).times ((((Geo.fixed 2).times h).joins (Geo.fixed 1)).power 5)).times (Geo.fixed _)).times (Geo.fixed _))
  have hv: Rate G L (-(1/2)) f:= by simpa only [zero_add] using! (hg.rate.mul Rate.flame)
  refine ⟨V,((Geo.fixed _).times hg).joins (Geo.fixed 1),?_⟩
  filter_upwards [hv.below (by norm_num) d hd, Sienna.puff G L 2 1 zero_lt_one] with x hv hK r hr P hx c g' h w hp u o F he
  have hf : 0≤ f x:= by have hh := P.threshold_pos.trans_le hx; unfold f g; have hz: 0<Pressure.fiery G x L:= pos_of_mul_pos_right hh (by norm_num); positivity
  have hj (y:Site c) (hy:separation o y≤Y x) (p : PlaqAxes): toll F (y,p) ≤ P.threshold:= by by_contra! hv; exact Finset.disjoint_left.mp he ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p),WilsonStartup.anchor_visit _,hv⟩)
  obtain ⟨a,ha⟩:= Work.E08.axial_patch o F w (Y x) hp h (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hx).le (fun y hy p=> (hj y hy p).trans hx)
  · let z (i:Site g'):= a (Slide.sites (Slide.cognac u) o i); let g':=Slide.shape (Slide.cognac u) o F
    have hb i (hi: separation o (i: Bond c).1 ≤ w): G.chord (Lattice.gauge a F i) ≤ f x := (ha i hi).trans_eq (by unfold f g; ring)
    let W:= gauge z g'; have he i:G.chord (W i) ≤ f x:= by
      unfold W g'; rw [show gauge z (Slide.shape (Slide.cognac u) o F)=_ from (Slide.shape_gauge (Slide.cognac u) o a F).symm]; unfold Slide.shape; split
      · exact hb _ (Slide.village ..)
      split; next h'=> rw [G.chord_inv]; exact hb _ (Slide.village ..)
      simpa [Gauge.chord] using hf
    obtain ⟨b,hb,hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (f x) hf ((le_abs_self _).trans hv) (fun i _=>he i)
    refine ⟨z,(Uniform.tint G _).symm b,?_,lt_of_le_of_lt (add_le_add ((Uniform.tint_inv_le _).trans hb) hK) ?_⟩
    · unfold Boulevard.actual; rw [ContinuousLinearEquiv.apply_symm_apply]; exact funext fun i=> (hQ i (by simp)).symm
    exact lt_of_eq_of_lt (show A*(f x)+1*Pressure.fiery G x L=V x*Pressure.fiery G x L from (by unfold V f; ring)) hr

lemma fixed (Y : ℝ→ℕ) (h:Geo G L fun x=>(Y x:ℝ)) : ∃ V : ℝ→ℝ, Geo G L V ∧∀ᶠ t : ℝ in atTop,
    ∀ β:ℝ,  (M t L)/2≤β ∧ β≤2*(M t L)→
      let r:= V t*gStep β
      0 < β ∧ 1 < V t ∧ d' t < r ∧ 0 < d' t ∧ r ≤ 1 ∧ Shore G L j t r ∧ Health G L (Y t) t r:= by
  obtain ⟨C,hC⟩:= Sluice.parcel G L j
  obtain ⟨A,hA,hV⟩:= Sluice.axially G L Y h
  let w x:= (|C|+|A x|+2)*Delay.fineMonitor G L x*2
  have hw: Geo G L w := (Geo.times (Geo.times (Geo.joins (Geo.joins (Geo.fixed _) (hA.mean)) (Geo.fixed _)) Geo.by_delay) (Geo.fixed _))
  refine ⟨w,hw,?_⟩
  filter_upwards [hC,hV,AuxMiles.upper_guard hw.rate, Sienna.puff G L 1 1 zero_lt_one,(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with t hC hV hv hf hy β hβ r
  have hx:0<M t L:=zero_lt_one.trans_le hy
  have ht:0<β:= (half_pos hx).trans_le hβ.1
  have hz:= Fare.gS β ht
  have he: 1 ≤ Delay.fineMonitor G L t:= Real.one_le_exp (sq_nonneg _); have h':1< w t := by unfold w; nlinarith [abs_nonneg C,abs_nonneg (A t)]
  have hl : Pressure.fiery G t L = gStep (M t L)*Delay.fineMonitor G L t:= rfl
  have hp: 0 < Pressure.fiery G t L:= hl ▸ mul_pos (Fare.gS _ hx|>.1) (Delay.monitor_pos _ _ _)
  have hR:r ≤ p' t:= hv β hβ.1 h'
  have hS : (|C|+|A t|+2)*Pressure.fiery G t L ≤ r:= by
    refine hl ▸ ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Geo.strip hx ht hβ.2) (zero_le_one.trans he)) (by positivity : 0≤|C|+|A t|+2)).trans_eq ?_); unfold r w; ring
  refine ⟨ht,h',?_, Real.rpow_pos_of_pos hx _, hR.trans (Real.rpow_le_one_of_one_le_of_nonpos hy vow_ok.le),hC r (mul_pos (zero_lt_one.trans h') hz.1) ?_ hR,hV r ?_⟩
  · rw [one_mul] at hf; nlinarith only [hp,hS,hf,mul_nonneg (abs_nonneg C) hp.le, mul_nonneg (abs_nonneg (A t)) hp.le]
  · exact le_trans (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith [abs_nonneg (A t)])) hp.le) hS
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith [abs_nonneg C,le_abs_self (A t)] : A t < |C|+|A t|+2) hp) hS
end YM.RGComparison01.Sluice
