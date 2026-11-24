import YM.AllOrder.Transit.Picnic
import YM.QuadraticLocal.Vacuum.Calorie
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
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm
open Burn Carillon Cap Rosary.Repair Moon Moon.Kit
open Floe
open Step PlanV
variable {G:Gauge}{X: Metals G} {D: Rolls X.p} {C' : Targets X.p X.K} {Z :Expenses C'} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v) {i j:ℕ}
variable {P:Protection D}

/-!
# The post-block chronology extension for general e

`Curriculum` delays driving the explicit local estimate. Reuses the base
whole-year scheduling proof with the puts for any supported correction in
`Candor`. The isolated E is charged explicitly at the rate `W/L`, not
merely the `heap` rate of pay in `Year`. `attenuation = βhat^{-1/80}`.

No `Stamp` or `Scene` is asserted by these gates; those are supplied by
the existing chosen Run from the concrete near/far and sector estimates.
Adapted from `YM/AllOrder/Transit/{Lease,Picnic}.lean`.
-/
section earns
variable {G:Gauge} (S:Sheet G) (K : MapPrices) (M : Targets S K) (Q:Expenses M) (f:ℕ→ℕ)
def Facility (f:ℕ→ℕ) := ∀ (x y:ℕ),StepStages x y→∀ L:Side,f x≤L.val→∀ k:ℕ,k ≤ y →∀ (W μ c:ℝ)(o:Target.Order G W), 0<W→0<μ→ (M x y).rate < -(3/8:ℝ) → ∀ (j n:ℕ), ∀ᶠ t in atTop, High.Meets (M x y) k L (Q x y) W μ c o j n Chi.canonical t
lemma wagesWanted (S:Sheet G)(K:MapPrices)(M : Targets S K)(Q:Expenses M): ∃ f,Facility S K M Q f:= by
 choose m hm using fun x y k=> allowsMultiplier (M x y) k
 let f x y:ℕ:=Finset.sup (range (y+1)) (fun k=>m x y k)
 refine ⟨fromMax f,fun x y h L hL k hK W μ c o hw hμ hk j n=> hm x y k L ?_ _ _ _ _ o hw hμ hk j n _⟩
 exact (le_sup (s:=Finset.range (y+1)) (f:=fun k=>m x y k) (by simp; omega : k∈Finset.range (y+1))).trans ((le_fromMax f h).trans hL)
end earns
section crispPaper
variable {J:Teller G} {A: ConnectedActivityE6.Target G J} {Lc:Side} (M:JointLoad.Heir.Record) (χ:Chi){ν:ℕ} (Z:Libretto G ν)
    {U α g :ℝ}{k m:ℕ}(W:Stage)
structure YearSharp (o:ConnectedActivityE6.Target.Order G U) (α t ε:ℝ)(k:ℕ)(A: ConnectedActivityE6.Target G J)(Lc:Side): Prop where
 stays : ∀ (c d:Side)(S':StepData c d)(T':Tube G S'), Works J Lc t S' T' → ∀ (R:RG.Rep G d)(μ c':ℝ)(H:Cash U t μ Lc A o c' T' R) (B:BudgetPoint), B.B=radiusB t→ B.power=W.power→ Plays Z M B R.p J T' t→ A.halo+5≤k→ Release.accepts k R.p.supportExponent ε Lc→ Release.Quotation Z W.power k R.p.supportExponent ε α → Lute.Plented Z M B R.p Lc k t (gStep R.beta)→ ∀ j≥ν, ∀ (C' d h Y A b r B₀ q : ℝ) (l : ℕ), Captain H j C' d h Y A b r B₀ q l Chi.canonical → ∀ q κ', ∀ (X:Set ℕ) (c δ:ℝ), Candor R.p R.activities X c δ→ 0≤δ→δ≤ incomingE G Lc t → Brim.Homes X H M q χ Chi.canonical κ' B ε (α / (Lc.val:ℝ)*δ) (High.attenuation (betaF G t Lc)*δ)
lemma springSharp (hG:G.Simple)(hε:M.ε ≤ 1/4)(o:ConnectedActivityE6.Target.Order G U) (hk:2≤ν)  (v:ℝ)(he: 0≤ v) : ∀ᶠ x in atTop, YearSharp M χ Z W o α x v k A Lc:= by
 by_cases h:∃ D:Patch,D.L=Lc ∧ D.J=J.j ∧ D.Branches J.bind G; swap; · exact Eventually.of_forall fun t=> ⟨fun c f S T h' => (h ⟨S.patch,h'.length_eq,h'.funds.atStep,h'.funds.kernel⟩).elim⟩
 obtain ⟨D,h,hD,hF⟩:= h
 obtain ⟨p,hv,hx⟩:= Brim.selectiveP G hG J Lc D hF W.power ν Z M hε hk Chi.canonical χ U o v k he;
 filter_upwards [hx,hv _ (by norm_num : -(1/2:ℝ)< -(1/80:ℝ))] with i hi ht; refine ⟨fun cX dX Sℓ Tℓ hW R μ c' H B hB hb hp ha hv hr hz j hj C' d hE Y A b r B₀ q l N qξ κ' X c δ hS hd hh=>?_⟩
 obtain ⟨⟨u,hp',hy,H₁⟩,w,H,hH,hL⟩:=hi cX dX Sℓ Tℓ (hW.patch h hD) hW _ _ _ _ H B hB hb hp ha _ hv hr hz j hj A b d Y C' B₀ r hE q _ N qξ κ' X c δ hS hh -- duplicate variables. use renamed.
 exact ⟨⟨u,hp',hy,fun i=> budget_loosen (H₁ i) le_rfl⟩, w,fun i=>budget_loosen (H i) (mul_le_mul_of_nonneg_right ht hd),hH,hL⟩
end crispPaper

variable (W:Return.Wages)(C:Programs X.p)(E:Return.Wages)(r:ℕ→ℕ→ℕ)(q:ℕ→ℕ→JointLoad.Heir.Record) (κ:ℕ→ℕ→Chi)
abbrev vanishes (x:ℝ):= x ^ (-(1/160):ℝ)
-- cores for all-mark employments after normalizing analytic labels.
abbrev cores (j i:ℕ)(k:ℕ) (t:ℝ): Prop:=
    High.Meets (C' j i) k (D.L j) (Z j i) (p j i) (R.μ j i) (R.c j i) (R.o j i) (X.p.profile i).order (X.p.profile i).power Chi.canonical t

def witnessPrice (G:Gauge)(L:Side)(t:ℝ)(S:Stage)(k g:ℕ)(V:BudgetPoint):ℝ :=
      away S*(2*pen G L k t 0 + pen G L k t 0)+pen G L k t 0 + turnFee V *footprint G L t S k g V
abbrev orderTarget (x:ℝ)(k:ℕ):= x ^ (-(Burn.horizon k+2:ℝ)/2)
lemma post_actual (G:Gauge)(L:Side)(S:Stage)(g k:ℕ): ∀ᶠ t:ℝ in atTop, ∀ (B:BudgetPoint), Time.Same S B→
    witnessPrice G L t S k g B ≤ orderTarget (betaF G t L) k:= by
 let T:=Burn.credit k; let J:=(Burn.credit k-1/80+(1/400:ℝ)); let Y:= (Time.probe S); let u x:=turnFee Y* footprint G L x S k g Y; let f'(x:ℝ):=pen G L k x 0; have he: Rate G L J f':= Rate.weaken Rate.power (by unfold J; linarith); let hv:=funds G L S k g; have ht: Rate G L J u:=((hv.mul_right _).mul_left _); have hE:= ((((he.mul_left 2).add he).mul_left (away S)).add he).add ht;
 filter_upwards [hE _ (by unfold J; rw [Burn.sale_eq]; linarith : J < -(Burn.horizon k+2:ℝ)/2)] with t ht B hb
 unfold witnessPrice; rw [Cap.foyer G L t S k g B hb]; exact (le_abs_self _).trans ht
lemma contract_factor (G:Gauge)(L:Side)(S:Stage)(Q:ℝ)(h:0<Q): ∀ᶠ t:ℝ in atTop, let x:=betaF G t L; 2*away S* attenuation x ≤ vanishes x ∧ vanishes x≤Q:= by
 filter_upwards [(Rate.power (G:=G) (L:=L) (a:=-(1/80:ℝ))|>.mul_left (2*away S)) (-(1/160:ℝ)) (by norm_num), (Rate.power (G:=G) (L:=L) (a:=-(1/160:ℝ))).below (by norm_num) Q h] with t ht hz; exact ⟨(le_abs_self _).trans ht,(le_abs_self _).trans hz⟩

structure Deep (j i:ℕ)(t:ℝ): Prop where
  opens : ∀ k ≤ i, cores R j i k t∧ ∀ B:BudgetPoint, Time.Same (X.p.profile i) B → witnessPrice G (D.L j) t (X.p.profile i) k (Shop.parking (Shop.tall i) (C' j i).halo) B ≤ orderTarget (betaF G t (D.L j)) k
  oldE : X.p.first ≤ i → YearSharp (q j i) (κ j i) (C j i) (X.p.profile i) (R.o j i) (W j i) t (Psalm.Solo.raise E j i) (r j i) (C' j i) (D.L j)
  minor : (2*away (X.p.profile i))*attenuation (betaF G t (D.L j)) ≤ vanishes (betaF G t (D.L j))∧ vanishes (betaF G t (D.L j)) ≤ (Time.credit G (X.p.profile i))/16

structure Lock (W': Delays P):Prop where
  actor : ∀ t j i,W'.betaEntry j ≤ t → StepStages j i → Deep R W C E r q κ j i t
  senior : ∀ j i,StepStages j i → W j i / ((D.L j).val:ℝ) ≤ heap G (X.p.profile i) (1/16)
local notation "S" => X.p
set_option maxHeartbeats 800000 in
lemma locks (g:G.Simple) (hl:Facility S X.K C' Z X.p.floorL)(hS:Roof.wantFacet X.p W (1/16) X.p.floorL)(hq:∀ j i,StepStages j i → (C' j i).rate < -(3/8:ℝ))(hf:∀ j i, StepStages j i→0≤E j i)(hp:∀ j i,StepStages j i→ X.p.first ≤ i → (q j i).ε ≤1/4) (V:Delays P) : ∃ W':Delays P, DelayLe V W'∧∀ V',DelayLe W' V'→ Lock R W C E r q κ V':= by
 have ht (j i:ℕ)(h:StepStages j i) : ∀ᶠ x:ℝ in atTop, Deep R W C E r q κ j i x:= by
    let P:= X.p.profile i; let L:=D.L j;
    have hv (k:ℕ)(hk:k≤ i): ∀ᶠ x:ℝ in atTop, cores R j i k x ∧ ∀ B:BudgetPoint, Time.Same P B → witnessPrice G L x P k (Shop.parking (Shop.tall i) (C' j i).halo) B ≤ orderTarget (betaF G x L) k:= (hl j i h L (D.large j).need k hk _ _ _ _ (R.consumes j i h).1 (R.consumes j i h).2.1 (hq j i h) _ _).and (post_actual G L P _ k)
    have he : ∀ᶠ x:ℝ in atTop, X.p.first ≤ i → YearSharp (q j i) (κ j i) (C j i) P (R.o j i) (W j i) x (Psalm.Solo.raise E j i) (r j i) (C' j i) L:=by
       by_cases h':X.p.first ≤ i; · exact (springSharp _ _ _ _ g (hp j i h h') (R.o j i) (le_trans (by decide : 2≤6) (X.p.profile i).order_ge) (Psalm.Solo.raise E j i) (add_nonneg (hf j i h) zero_le_two)).mono fun x hx _=>hx
       exact Eventually.of_forall fun _ he=> (h' he).elim
    have hb:= contract_factor G L P ((Time.credit G P)/16) (div_pos (Time.credit_pos ..) (by norm_num))
    filter_upwards [(Filter.eventually_all_finset (Finset.Iic i)).mpr (fun k hk=> hv k (Finset.mem_Iic.mp hk)),he,hb] with x hx ht hv; exact ⟨fun k hk=>hx k (Finset.mem_Iic.mpr hk), ht,hv⟩
 obtain ⟨t,-,hx,hy⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (ht j)); exact ⟨{V with betaEntry:=t},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Z h=>⟨fun t j i he hi=>hy _ _ ((h.beta j).trans he) i hi,fun j i he=> hS i j _ he (D.large j).need⟩⟩

end YM.AllOrder.Transit
