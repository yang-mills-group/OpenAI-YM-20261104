import YM.AllOrder.Horizon.Pair

/-!
# Sub-stencil prediction allowances after allocated height.

Debit old cap & support weights and mask-mergers, eaves used for ordinary
Wilson (first order) limit and small-ratio for later full comparison.
No caller can use `rising` at budget radius ~`r`, a **separate** proof (Dust).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} (D: Rolls X.p) {C : Targets X.p X.K} {Z :Expenses C} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v) {i j:ℕ}
    {P : Protection D} (A : PostCost D)

def most_side (D:Rolls X.p)(C:Targets X.p X.K)(j i:ℕ)(t:ℝ):ℝ:= (Trio.paySide G (D.L j) (Shop.parking (tall i) (C j i).halo) t:ℝ)
def slope_post (j i : ℕ) (x:ℝ):Prop := let L:= D.L j; let t:= (Z j i).wanting; let b:= parking (tall i) (C j i).halo; let T:= X.p.profile i; let B:=radiusB x; let h:= Trio.base b B
    (Marlin.tithe (2*h) (Trio.lossFee G L t b T x) ⟨T.power,T.order,T.supportExponent,1,1,T.power_ge,T.order_ge,T.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicket b) ≤ betaF G x L ^ (-(1/8:ℝ)))∧
    (let u:=gold G L x; let z:= Height.away T; z*u+u+ z*(planks G L b T x* Real.exp (Trio.stout T * coverTicket b)) ≤ (1/2:ℝ)*(Time.credit G T*δE x)) ∧
    Pane.Morning D R A (most_side D C) i j (X.p.profile i).order x ∧ ∀ P:BudgetPoint,P.threshold ≤2*Pressure.fiery G x L→∀ c f: Side, 2*h<c.val→∀ w:ℕ,w+1≤h→∀ (u:2*w≤f.val) (o:Site c) (V:Config G c), Healthy P.threshold (neighbors h o) V→ ∃ (z:Site f→G.El) (s:Positions (Uniform.Primary f G)), Boulevard.actual s=gauge z (Slide.shape (Slide.cognac u) o V) ∧ ‖s‖+2*Sienna.furl G L x < eaves G L x
lemma posts_extra (h: StepStages j i) (ht:(Z j i).wanting=-(7/16:ℝ)):∀ᶠ x in atTop, Shop.slope_post D R A j i x:=
  let b:= parking (tall i) (C j i).halo; let L:=D.L j; let p:= (X.p.profile i)
  (Trio.cheap G L _ b p ht).and ((Roof.compar G L b p).and ((Pane.shouts D R A (most_side D C) h ((show 2≤6 by norm_num).trans p.order_ge) (Trio.circles ..)).and (Trio.pledges G L (fun x=>Trio.base b (radiusB x)) (Trio.rows G L b|>.2.2.1.uses))))

def Snow (W:Delays P):= ∀ j x,W.betaEntry j≤x → ∀ i, StepStages j i → slope_post D R A j i x
lemma budget_extra (V:Delays P) (hf: ∀ j i,StepStages j i→ (Z j i).wanting= -(7/16:ℝ)) : ∃ U:Delays P, DelayLe V U∧ ∀ W:Delays P,DelayLe U W → Snow D R A W:= by
  obtain ⟨x,-,hv,hV⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi => posts_extra D R A hi (hf j i hi)))
  exact ⟨{V with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun Z h j t ht i hi=> hV j t ((h.beta j).trans ht) i hi⟩

end YM.AllOrder.Shop
