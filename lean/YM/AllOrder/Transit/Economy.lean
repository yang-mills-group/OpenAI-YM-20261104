import YM.AllOrder.Transit.Lease
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Transit
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace Moon
open Burn Carillon Carillon.Cap Rosary.Repair
variable {G:Gauge} {c f L:Side}{S:Stage} -- scrub
variable (G L S)(H:ℝ)
local notation "K"=>S.width
local notation "C"=> S.paths
local notation "X"=> fun t:ℝ=> betaF G t L
abbrev stamp (G:Gauge)(L:Side)(S:Stage)(P:BudgetPoint)(Λ β α:ℝ):ℝ:= Song.octaveNeed G P S.clip S.width S.paths Λ β α
lemma dual (P:BudgetPoint)(Λ:ℝ)(hp:0≤Λ)(β b:ℝ): stamp G L S P Λ β b ≤ 2 * stamp G L S P Λ (β/2) b := by
    let v:=(-β:ℝ); have he(i:ℕ) (c:ℝ): tenor G i P K c (- (β/2))=(1/2:ℝ)*tenor G i P K c (-β):= by unfold Song.tenor; rw [← neg_div, ← mul_div_assoc, abs_div]; rw [abs_of_pos (show 0<(2:ℝ) from zero_lt_two)]; ring -- neg_div orientation?
    let u k:= anchoredFee (headline P) k; have hk k:0≤ u k := by unfold u anchoredFee; positivity
    have ht k:0≤ highFee G k P K:= (highFee_pos G P k S.width_pos).le; have hP₀:=turnFee_pos P; have hP:= P.threshold_pos; have hz:0≤u (Song.octave 2)*tenor G 2 P K Λ (-1):= by unfold tenor; specialize hk (octave 2); specialize ht 2; positivity
    have hf:0≤u lowCount*host G S.clip P K C (-b):= by
       have hs:=lowFee_nonneg G P S.width_pos; unfold Song.host; specialize hk lowCount; have h : 0≤ lowerSize S.clip C:= by unfold lowerSize; have hx:= S.clip.quadratic_pos; have hv:= S.paths_pos; positivity
       positivity
    unfold stamp Song.octaveNeed; rw [he,he]; unfold u at *; linarith only [hz,hf]
lemma transit_model (k:ℕ): ∀ᶠ t in atTop,∀ (p:BudgetPoint), Time.Same S p→p.B=radiusB t→p.threshold=temp t→∀ v:ℝ,Burn.Near t v→PostP.C' p G k v t ≤ Cap.fee1 G L t:= by
 let T:= S; let Δ:= (fun x:ℝ=> betaF G x L); let H:= Burn.stop (G:=G) (Floe.Age.scope (Burn.horizon k+2)) T 0 (Burn.horizon k); filter_upwards [budgets_x H (by norm_num : -(3/2:ℝ) < -(1:ℝ)), eventually_gt_atTop (1:ℝ), eventually_ge_atTop (G.slopeConstant*Real.log L.val), eventually_ge_atTop (2:ℝ)] with i hi ht hD he p hv hb hp v hq; unfold PostP.C'; rw [Till.Tilt.sameprice, hv.1,hv.2.1,hb,hp]; refine ((le_abs_self _).trans (hi v hq)).trans ?_; rw [fee1]; have hX : Δ i ≤ i^2:= (by unfold Δ Pressure.betaF; nlinarith only [he,hD]); have hζ:1≤ Δ i:= ht.le.trans (le_add_of_nonneg_right (Work.E04.shift_nonneg G L)); change (i:ℝ)^(-(1:ℝ)) ≤ Δ i ^ (-(7/16:ℝ))
 refine le_trans (b:= (i^ (2:ℕ))^ (-(7/16:ℝ))) ?_ (Real.rpow_le_rpow_of_nonpos (by linarith) hX (by norm_num)); rw [← Real.rpow_natCast_mul (by linarith : 0≤ i)]; apply Real.rpow_le_rpow_of_exponent_le ht.le; norm_num
-- purchase Width path. Need PNotes comparison μ. future plus start.
variable (k g:ℕ)
structure Buoyant (t:ℝ): Prop where
    predicts : ∀ B:BudgetPoint,Time.Same S B→B.threshold=Pressure.temp t→B.B=radiusB t→Width (Rosary.pearl B) S.clip S.width∧4*(horizon k+4) ≤ B.B ∧
      HorizonW G L t S k g B ∧ (∀ v:ℝ,Near t v→ PostP.C' B G k v t ≤ Cap.fee1 G L t) ∧ (B.threshold≤2*Pressure.fiery G t L→∀ β b Λ,|β| ≤ 4*(betaF G t L)→|b| ≤ H→0 ≤ Λ→Λ ≤ ConnectedActivityE6.loopBill G L t → Song.octaveNeed G B S.clip S.width S.paths Λ β b ≤ 2*fee1 G L t∧ Real.exp (-(S.width/4)* ↑B.B)*Song.octaveNeed G B S.clip S.width S.paths Λ β b ≤ pen G L k t 0)
    solves A : PostP.Checks G S k H (A:PostP.Actor G S k H t)
local notation "ζ"=> credit k-1/80+0
lemma forecasted (h:0<H) : ∀ᶠ t:ℝ in atTop,Buoyant G L S H k g t:= by -- order verify
 let F:= (Rate.power (a:=ζ-1) (G:=G) (L:=L)|>.mul_left 2);
 filter_upwards [Meadow.flights G L S H h,PostP.backed G S k H, transit_model G L S k, Shop.dues G S L _ (ζ-1) h,PostP.prefer S, constr G L S k g, Work.E01.radiusB_tendsto.eventually_ge_atTop (4*(Burn.horizon k+4)), F ζ (by linarith)] with t ht hu hv he hF hC hW hk; refine ⟨fun B hb hp hx=> ⟨hF B hb hx,hx.symm ▸ hW,hC B hb,hv B hb hx hp,fun ha β b Λ hβ hγ hz hq=>?_⟩,hu⟩
 have hs:|β/2| ≤ 2*betaF G t L:= by rw [abs_div,abs_of_pos (show 0<(2:ℝ) from zero_lt_two)]; linarith only [hβ]
 refine ⟨le_trans (dual G L S B Λ hz β b) (mul_le_mul_of_nonneg_left ((ht B ha hb.1 hb.2.1 hb.2.2 hx _ _ _ hs hγ hz hq).1) (by norm_num)), le_trans (mul_le_mul_of_nonneg_left (dual G L S B Λ hz β b) (Real.exp_pos _).le) ?_⟩
 rw [mul_left_comm]; exact (mul_le_mul_of_nonneg_left (he B ha hb.1 hb.2.1 hb.2.2 hx _ _ _ hs hγ hz hq) zero_le_two).trans ((le_abs_self _).trans hk)
end Moon
end YM.AllOrder.Transit
