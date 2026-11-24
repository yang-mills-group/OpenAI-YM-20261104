import YM.AllOrder.Horizon.Pass
/-! # Predict small-radius aligned stencil from Shape condition. Step ledger extension of Viewers. -/
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
lemma rising_slender (h0 : -(1/2:ℝ)<η) (hU : η*2< -(1/2:ℝ)) (j : ℕ) : ∀ᶠ x in atTop,∀ (P: BudgetPoint), P.threshold=Pressure.temp x → P.threshold ≤ 2 * Pressure.fiery G x L → P.order=j →
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
  have hw: Rate G L η w:= (Rate.power (a:=η) (G:=G) (L:=L)).mul_left _
  let g x:=4*(sunLength p (w x) * r)
  have hg : Rate G L η g:= ((((hw.mul_left (1+1)).mul_left _).mul_right _).mul_left _)
  filter_upwards [Delay.shift_pos G L, Sienna.below' G L hw (show η<0 by linarith only [hU]) hc,hw.below (show η<0 by linarith only [hU]) 1 zero_lt_one,
    Sienna.contraction G L (a:=r) (b:=r) hr (p:=η*2) (hg.pow 2) hU, softly G L, hR.below (by norm_num) 1 zero_lt_one,
    Sienna.contraction G L (a:= j.factorial*J) zero_lt_one hR h0] with
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
end YM.PhysicalNext.Repeat.Boulevard

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
lemma pledges_slender {e:ℝ} (hu : -(1/2:ℝ)<e) (G: Gauge) (L: Side) (Y:ℝ→ℕ) (h: Rate G L 0 fun x=>(Y x:ℝ)): ∀ᶠ x in atTop, ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2* Y x<c.val→∀ w:ℕ,w+1≤Y x→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors (Y x) o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < betaF G x L ^ e:= by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let f x:= 16*(2*(Y x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hv : Rate G L (-(1/2)) f:= by
    simpa only [f,zero_mul,zero_add] using! (((((h.mul_left 2|>.add (Rate.const 1)).pow 5).mul_left _).mul_right _).mul ((Rate.flame (G:=G) (L:=L)).mul_left 2))
  filter_upwards [hv.below (by norm_num) d hd, contraction G L (a:=1) (b:=1) zero_lt_one ((hv.mul_left A).add ((Sienna.belt G L|>.mul_left 2).weaken (by norm_num))) hu] with x hv hK P hx c g h w hp u o V he
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

namespace YM.AllOrder.Shop
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} (D: Rolls X.p) {C : Targets X.p X.K} {Z :Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v) {i j:ℕ}
    {L : Side}

def interest (_j i:ℕ):= ((16*(1+(i:ℝ))))⁻¹
def edgeW (i:ℕ) := interest 0 (i+3)
def air (i:ℕ):= -(1/2:ℝ)+edgeW i / (4+(i:ℝ))
def output (k:ℕ) (e:ℝ) := -(1+(k:ℝ))/2+e
local notation "z'" => (fun x=> betaF G x L)
local notation "z0" => (fun x=> z' x^air i)
lemma interest_ok (i j:ℕ) : 0 < interest i j:= by unfold interest; positivity
lemma edge_pp (i:ℕ) : 0 < edgeW i := interest_ok ..
lemma buys_air (i:ℕ) : -(1/2:ℝ)<air i ∧ air i < vow := by
  have he:= edge_pp i
  constructor
  · unfold air; exact lt_add_of_pos_right _ (by positivity)
  have hi: edgeW i ≤ (1/16:ℝ):= by
    unfold edgeW interest; rw [one_div]; apply inv_anti₀ (by norm_num); exact le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))
  unfold air vow; have hc:4≤4+(i:ℝ):=le_add_of_nonneg_right (by positivity); nlinarith [div_le_div_of_nonneg_left he.le zero_lt_four hc]

-- formulas kept abstract? Snow `interest chosen edgeW`. output η': 3*edgeW approximate. reserve ζ maybe ∥script∥ expected `hatPeices`. fBound model ≤ ε^(k+1?)` enough. true clearance price throughput of turn costs.
def gainC (G : Gauge) (L : Side) (P:Stage) (b i k :ℕ) (x:ℝ) : ℝ :=
    let z:= betaF G x L; let y := z^(air i); let d:= z^(edgeW i)*(z*y^(k+3)+y^(k+1))+ z^(seam_hat i)
    2*d+z^ output k (edgeW i)

def creditC (G : Gauge) (L : Side) (P:Stage) (b i k:ℕ) (x:ℝ) (t:Stars) : ℝ:= ticket P.order (gainC G L P b i k x)+2*((Fintype.card (Site (fence b (radiusB x) t)):ℝ)* (betaF G x L)^ seam_hat i)

def priceC (G : Gauge) (L : Side) (P:Stage) (b i k :ℕ) (x:ℝ) : ℝ:=∑ j:Stars, |Slide.ray j| *((2:ℝ)^P.order*((1+(Trio.base b (radiusB x):ℝ))^(P.power*P.order))*Shop.creditC G L P b i k x j)
lemma weightC (P:Stage) {k:ℕ} (h:k ≤ i) (b:ℕ) : Rate G L (output k (3*edgeW i)) (priceC G L P b i k) := by
  let g:=output k (3*edgeW i); let a:=edgeW i; have hp : 0 < a:= edge_pp _
  have he': seam_hat i ≤ g:=by unfold g seam_hat output; nlinarith only [hp,show (k:ℝ) ≤ i from (by exact_mod_cast h)] -- hp unfold
  have hp': (4:ℝ)+(i:ℝ)>0:=by positivity
  let b':= a/(4+(i:ℝ)); have hb:0<b':=by unfold b'; positivity
  have he:(k:ℝ)*b'+3*b' ≤ a:= by
    have hz : (4+(i:ℝ))*b'=a:=by unfold b'; field_simp
    nlinarith only [hz,hb,mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ (i:ℝ) from (by exact_mod_cast h)) hb.le]
  have hu: Rate G L (g-a) (fun x=> z' x*z0 x^(k+3)+z0 x^(k+1)):= ((Rate.hat.mul (Rate.power (a:=air i) (G:=G) (L:=L)|>.pow (k+3))).weaken (by unfold air g output; push_cast; unfold b' at he; unfold a at *; linarith only [hp,he])).add ((Rate.power.pow (k+1)).weaken (by unfold air g output; push_cast; unfold b' at he hb; unfold a at *; linarith only [hp,hb,he]))
  have hv := Rate.power (G:=G) (L:=L) (a:=seam_hat i)|>.weaken he'
  have hx : Rate G L g (gainC G L P b i k):= by unfold gainC; dsimp only; exact (((Rate.power.mul hu|>.weaken (by linarith)).add hv).mul_left _).add (Rate.power (a:=output k (edgeW i))|>.weaken (by unfold g output; linarith only [hp]))
  have hY : ∀ t:Stars,Rate G L g (fun x => creditC G L P b i k x t):= fun t=> by
    simpa only [zero_add] using! ((hx.mul_left ((P.order.factorial:ℕ):ℝ)).mul_right ((1+ (1+1):ℝ)^P.order)).add (((Trio.feeStars G L b t).mul hv|>.weaken (zero_add g).le).mul_left 2)
  unfold priceC; refine Trio.sparks G L ?_; intro j
  simpa only [zero_mul,zero_add] using! ((((((Rate.const 1).add (Trio.rows G L b|>.2.2.1.uses)).pow (P.power*P.order)).mul_left ((2:ℝ)^P.order)).mul (hY j)).mul_left |Slide.ray j|)
end YM.AllOrder.Shop
