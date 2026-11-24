import YM.Qlocal.Versal.Wager
/-!
Instantiate the universal primitives at a scheduling lease in the purchased currency.
Available at the Guide for any admitted period & construction-cutoff. Reclosure
trace tickets use the same θ. The support exponent ticket buys at least +3
at this entry, of which +2 is needed for two packings at that step. Strong CP.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Leasing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
open RGComparison01 RGComparison01.Pledge
open Checks Baked Palette Pillow Resin Season Ink Switch Mallow Ovens OmitClusters Song Refrain Motion Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Push.Uniform Sienna Fare Lapis
open Holdings
open Tensor WilsonStartup Presented Planned.JetPort Ovens
open RG.Shoot
variable {M:Metals G}{R':Rolls M.p}{A:Alloy M R'} (F:Roost.Factor A)
    {m N p:ℕ} {η:ℕ→ℝ} {u:ℕ→ℕ}
local notation "C₀"=> A.B.a
set_option quotPrecheck false
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> (Mural.sheet M.p R' ((C₀).clock.adm (m+1)))
local notation "x₀"=> (C₀).clock.hatBeta m
local notation "θ"=> (C₀).budget m
local notation "μ₀"=> F.shape.μ J I
local notation "L★"=> R'.L J
local notation "F'"=> (F.target J I)
local notation "ℓ★"=> (F.expense J I)
variable (η) (B':Bauble G (R'.L (A.B.a.clock.J (m+1)))) (hB : Opened F η k j m B')
local notation "s"=> θ.supportExponent
local notation "λ★"=> β -- placeholder
variable (hz:f.val=c.val*(A.B.a.S.block m).val){R:RG.Rep G f} (C:Boulevard.Chartlet F.shape A N m hz R) (hm:m<N)
    {L : ι → Lotus.Leaf R}
local notation "O₀"=> Chi.canonical
include hB hm
lemma served [Fintype ι] (g:ι→ℝ)(hg:∀ i,0≤g i): Lanes.Shed C L g (A.B.a.budget m) Chi.canonical:=by
 have hv: (Pane.panel A m hz).patch=Y:= C.laws.data.funds.patch rfl rfl; have hh:=(hB.paid _ (A.B.valid.pays _)).permission; rw [← hv,(Rain.jersey (A:=A) (m:=m)).1.symm, (Rain.jersey (A:=A) (m:=m)).2.1.symm] at hh; exact Lanes.stint C L g _ rfl (Pane.ovation A N hz hm F.pledging.conducts.full) hh hg
omit hm
open Quipu.Sonnet
open Stowe Luggage RGComparison01.Pledge.Hoboken
variable {C1 F1:Side}{w0 M₁ n' :ℕ} (h1:F1.val=C1.val*(A.B.a.S.block m).val)
local notation "Dμ"=> Library.deck c C1
local notation "Dm"=> Dμ*(A.B.a.S.block m)
local notation "Fq"=> (show (Dμ).val=c.val*C1.val from rfl)
local notation "Lq"=> (show (Dμ).val=C1.val*c.val from mul_comm ..)
variable (x:Site (Library.deck c C1))
def trope : Site c:= splitter (Deck.divides Fq) x
-- choose second trench `X1`. Memory.A.Volume.Sub.Dis.
def trove : Site C1:= splitter (Deck.divides Lq) x
local notation "F₀"=> trope x
local notation "S₀"=> trove x
local notation "Yb"=> neighbors n' F₀
local notation "Tμ"=> Pane.panel A m h1
local notation "T₀"=> Pane.panel A m hz
variable {Ω:Type}[Fintype ι]
variable {U: RG.Rep G F1}{β:ℝ} (K:Chartlet F.shape A N m h1 U) (hK: SeekR F.shape A N m h1 K)
    {M1:ι→ Lotus.Leaf U} {D : Ω→ι→Lotus.Leaf R}{D': Ω→ι→Lotus.Leaf U} (h:Roster M1 D')(hP:Library.Visible A m N hz R β) (hU:Library.Visible A m N h1 U β)
local notation "Xs"=> Positions (Uniform.Primary C1 G)
variable (u0:ℝ) (g:ι→ℝ) (hg: Bench M1 g (B'.mass (A.B.a.clock.hatBeta m)))
   (Q Q':Type)
   (Φ: Ribbon R n)(P':Ribbon U n)(hc :4*M₁+16 ≤ c.val)(hc1:4*M₁+16 ≤ C1.val) (z:ι) (p:Finset ι)(hp:z∈p)
   (κ₀ : Ω→ Config G C1→ℝ) (κ₁ : Ω→ Config G c→ℝ)
local notation "bak"=> Rotunda.bake (G:=G) (M:=M₁) (F₀) (S₀) (wcap _ _ hc1)
local notation "UΦ"=> Drawing.cabinet K P'
noncomputable abbrev Rebate (r t:ℝ):= Rotunda.priceP θ (2*M₁) (n'+M₁) * Leasing.zone (θ).order C1 r t -- unused M? notation captured
local notation "Hq"=> Leasing.scaleM (m:=m) B' C1 k e u0
local notation "Upage"=> zone (θ).order C1
abbrev resultO (P:BudgetPoint)(g:Site c)(n:ℕ) (f y : Ω→ Config G c→ℝ)(ν:ℝ) (Jt: Ω→ Config G c→ℝ) := ∀ x:Ω, PayR P (neighbors n g) ν (Jt x) ∧ ∀ V:Config G c, Healthy P.threshold (neighbors n g) V→ f x V=y x V+Jt x V
-- qFactor from Step `stampedFrame`. No assumption on actual ε and not requiring affordable Bench on real. But need Halo branch etc. Predictors pay later to use. This is at Warm-through-output. Need hC1 etc. Keep macro syntax out variable body.
local notation "D★"=> Drawing.cabinet C Φ
local notation "μ₁"=> budget (A.B.a) m
variable (hβ:β∈band A.B.a (m+1))(hE :(Tithe.portion U.activities Ψ).EBound U.p e) (he:e≤ incomingE G (R'.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))
include h hβ hE he hm hc1 hc hg hp hU hP hK
set_option maxHeartbeats 1000000 in
lemma chunk (hf:0 < u0)(hb:0 ≤ Upage r Hq)(hu:Drawing.Opens P' Ψ)(hl:∀ i,¬ Luggage.long M1 P' i)(hj:p.card ≤ w0)
    (hV:∀ x:Ω,(A.B.a.budget m).Regular univ (κ₀ x))
    (hW:Sluice.Shore G L★ (θ).order x₀ σ) (hW':Sluice.Health G L★ (2*M₁+1) x₀ σ)
    (hn:M₁+(2*M₁+1) ≤ n')(hl': 2*n'<c.val)(hd:Hoboken.std F m n (j+w0) ≤ M₁)
    (hL:∀ i:Ω,∃ (R': RG.Rep G Dm) (Z' : Ribbon R' n) (M': ι→Lotus.Leaf R'), Hoboken.Holo hz h1 R U (D i) (D' i) Φ P' x R' Z' M' z N β M₁ hc hc1)
    (hψ:∀ i:Ω,∀ V:Config G c, Healthy ((θ).threshold) (Yb) V→ κ₀ i (bak V)=κ₁ i V)
    (hv: ∀ x:Ω,∀ W:Positions (Uniform.Primary C1 G),‖W‖+2*Sienna.furl G L★ x₀ <σ→ Boulevard.actual W∈ Boulevard.sunny (A.B.a.budget m)→ Brush (A.B.a.budget m).order r σ⁻¹ ((Reels.allotV (D' x) g K p (χ:=Chi.canonical)-κ₀ x)∘Boulevard.actual) W):
    ∀ᶠ l in atTop, resultO θ (F₀) n' (fun x:Ω=> Stowe.tale (D x) g C D★ (j+w0) l p (χ:=Chi.canonical)) κ₁ (Rotunda.priceP θ (2*M₁) (n'+M₁) * Leasing.zone (θ).order C1 r Hq) (fun u:Ω=>(Stowe.tale (D' u) g K UΦ (j+w0) l p (χ:=Chi.canonical) - κ₀ u) ∘ (bak)):= by
 let t:= p; let V:= σ; have hy:p.Nonempty:= ⟨_,hp⟩; have he':0<j+w0:=by have hs:=Finset.card_pos.mpr hy; omega
 obtain ⟨h0,h1'⟩:= gains F η B' hB h1 K hK hm (hU.holds.symm ▸ hβ) h g hg hE he P' w0 p κ₀ hf hu hl hj hy hW hV hv
 have hr(i:ι):0≤g i:= by obtain ⟨v,hx,h,_⟩:= hg; exact h i
 have hq:3*M₁≤n':= by omega
 have hT : (θ).threshold ≤2*Pressure.fiery G x₀ L★:= by have hT:= K.laws.data.room.temperatures; rw [K.laws.data.funds.length_eq] at hT; exact hT
 filter_upwards [h1'] with l hl₀ i; let wcap₁:= zone (θ).order C1 r (Leasing.scaleM (m:=m) B' C1 k e u0)
 obtain ⟨R₀,Z₀,M₀,hΩ⟩:= hL i; obtain ⟨J',hJ'⟩:= Library.framed F rfl hm hΩ.views hβ
 let f:= Stowe.tale (D' i) g K UΦ (j+w0) l p (χ:=Chi.canonical) - κ₀ i
 have hw:(θ).Regular univ f:= CouplingShape.reg_sub (Meadow.regularA _ fun i' _=> CouplingShape.reg_extend ((h0 i).canopy _) (subset_univ _)) (hV _)
 -- need wcap₁≥0 from hl₀ using actual 0 admissible (maybe r radius ≤0 could fail). Sluice.Health ensures sample point for ANY Field Healthy. Use bake.tickets logic provides ∃ sample.We.Can instead require wcap input by miss.Root Act earlier. derive.
 have hw':0≤ wcap₁:=hb
 have ht(j)(h:j∈Yb):= Rotunda.tickets θ (F₀) (S₀) (wcap _ _ hc1) f (2*M₁+1) le_rfl hn hl' hT hW' hw hw' (hl₀ _ ) j h
 refine ⟨⟨(ht _ ((neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _))).1,Rotunda.reel θ F₀ S₀ _ _ hq hw, fun j hj=> ht j hj⟩,fun V hV'=>?_⟩
 have hz':= Hoboken.valley F hz h1 hc _ _ (D i) (D' i) g C K Φ P' hc1 x R₀ Z₀ M₀ z hP hU hΩ hd p hp J' (served F η B' hB _ J' hm g hr) he' hq V hV' (served F η B' hB hz _ hm _ hr) (h0 i) (k:=l)
 let V₀:= Stowe.tale (D' i) g K UΦ (j+w0) l p (χ:=Chi.canonical) (bak V); exact hz'.trans (show V₀=κ₁ i V+(V₀-κ₀ i (bak V)) from (by rw [hψ i V hV']; ring))
end YM.Qlocal.Leasing
