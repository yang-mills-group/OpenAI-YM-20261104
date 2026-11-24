import YM.RGComparison01.Marks.Holdings
import YM.RGComparison01.Ward.Pecan
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
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
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows Push.Uniform Sienna Fare Lapis
open Diner Vision Studio Extra.Iteration
open Fiord Estates Tensor WilsonStartup Presented Planned.JetPort
variable (P:Sponsor G)(U:Stipulation G)
namespace Holdings
variable {X:Metals G} {D:Rolls X.p}{Q:Targets X.p X.K}{E: Expenses Q}{v : ℕ→ℝ} {P₀:Return.Wages}(Z:PhysicalNext.Repeat.Register D E P₀ v)
variable (i j k m:ℕ)(hi : 4 ≤ j)
local notation "Y"=> (X.p.profile i)
local notation "Y'"=>(X.p.profile j)
local notation "L"=>D.L j
local notation "X₁"=>(P X D Q i j k)
local notation "X₂"=>(U X D Q i j k m)
local notation "Θ"=> (Q j i)
set_option quotPrecheck false
local notation "A"=> (Mural.sheet X.p D hi)
local notation "χ'"=>(Z.μ j i)
local notation "e"=> ((E j i).earn)
variable {Θ₀ : Protection D}
-- Resources universal before meshes. Ω cutoff arbitrary.P.G.
def qualify {X:Sheet G} {K : MapPrices} {Q : Targets X K} (Z : Expenses Q) (i j z:ℕ) := ∀ L':Side,z ≤ L'.val → ∀ R : Patch, R.Branches X.kernel G → ∀ W μ:ℝ, 0<W→0<μ → ∀ (o: Target.Order G W) (p k b:ℕ),∃ (U₀: Bauble G L') (k':ℕ), ∀ᶠ t in atTop, Checks.Cellar (Q j i) Chi.canonical W L' R o p k k' b μ (Z j i).earn (asset (Z j i)) U₀.mass U₀.pre U₀.roi U₀.miss U₀.invZ t
lemma priorBill {S:Sheet G} {K : MapPrices}{Q:Targets S K}(E: Expenses Q) (i j:ℕ): ∃ b, qualify E i j b := by
  obtain ⟨b,hM⟩:= Checks.bought G _ (Q j i) _ _ ((E j i).price) (asset_pos (E j i)) (show (E j i).earn +asset (E j i)+asset (E j i)≤(Q j i).exp from (by unfold asset; linarith only))
  refine ⟨b,fun L' hl r hr W μ hW hm o q v u=>?_⟩; obtain ⟨x,y,z,T,s,k,h,hp,hV,ht,hX,hq⟩:= hM L' hl r hr Chi.canonical μ W hm hW o q v u
  exact ⟨⟨x,s,z,y,T,h,hX,hV,hp,ht⟩,k,hq⟩
lemma moatF (ε:ℝ) (P' Z U V:ℝ→ℝ) (j:ℕ) (L':Side) (he:0<ε)(h:Geo G L' P')(hs:Geo G L' Z)(hp:Geo G L' U)(hv:Geo G L' V) : ∀ᶠ x:ℝ in atTop, ∀ β:ℝ,β>0→ betaF G x L'/2≤β→Moat j β ε (P' x) (Z x) (U x) (V x):= by
   filter_upwards [Geo.loss h he j,Geo.loss hs he 0,Geo.loss hp he 0,Geo.loss hv he 0] with x hx he hm hJ β hv hp
   refine ⟨(mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (Fare.gS β hv|>.1.le) _)).trans (hx β hv hp),?_,?_,?_⟩<;> first | simpa using (he β hv hp)|simpa using (hm β hv hp)|simpa using (hJ β hv hp)

lemma office (hp : StepStages j i) (k m:ℕ) (hk:1≤k) (b:ℕ) (hb:qualify E i j b)(hB:b≤ (D.L j).val) (η:ℝ)(hη:0<η):
    ∃ H:ℕ,∀ᶠ s in atTop, ∀ z≥H, Nonempty (Holdings.Quay P U Z i j k m hi η s z):= by
   let L₁:= D.L j; let q:= Z.o j i; have hΩ:=Z.consumes j i hp; let Y₁:=X.p.profile i; let Y₂:=X.p.profile j
   obtain ⟨ϕ,k',hS⟩:= hb L₁ hB (A) (X.p.has _) _ _ hΩ.1 hΩ.2.1 q Y₁.order (Fiord.heat k) Y₁.power
   -- local notations X with rebound k issue! explicitly let
   let S:=P X D Q i j k; let T:=U X D Q i j k m; let Zp:=Fiord.foyer (Θ).halo S.stencil (k'+m); let n:=Fiord.book S.inRank T.inMark T.outMark Y₁.order k
   have hc : Geo G L₁ (fun t=>(↑(2*Fiord.amp Zp t+1):ℝ)):= by
     have hA:= (Geo.fixed 2).times (Geo.basic ((Trio.rows G L₁ Zp).1))|>.joins (Geo.fixed 1)
     convert hA using 2 with x; norm_cast
   obtain ⟨r,hr,hR⟩:= Sluice.fixed G L₁ Y₁.order _ hc
   obtain ⟨X₀⟩:= Push.Uniform.pre_order G Y₂.width Y₂.paths (A).J X.p.kernel (n:=n+3) (by omega)
   let J:= (Θ); have hN : k+(T.inMark + S.inRank*k) < n:= by unfold n Fiord.book nBudget; omega
   obtain ⟨D',hd,hF⟩:= Kraal.Stereo.lacesS J q (A) X₀ Y₂.clip Y₁.clip (Trio.circles G _ Zp) (Classical.choice (Planned.JetPort.purchase J.table J.table_exists _)) (Classical.choice (BareRates.offered G Y₁.width Y₁.paths _)) hΩ.2.1 hN (by unfold n Fiord.book nBudget; omega : k+2<n) (by unfold n Fiord.book nBudget; omega : Y₁.order<n) hk
   let W := T.dollars Zp ϕ.mass ϕ.invZ ϕ.pays_mass ϕ.positive D' r hr
   let X':= W.originBill
   obtain ⟨T₀,T₁,T₂,t₃,h₀,h₁,h₂,hx₃,hJ⟩:= hF r X'.f W.aperture W.shelter hr X'.ease W.wing W.head X'.const X'.letters W.growth
   obtain ⟨Xw⟩:= Ward.polarized G (Y₁.order+1)
   obtain ⟨R,hρ,hf'⟩:= Xw.bulk_head («L»:=L₁) Zp r hr
   let V := T.dollars Zp ϕ.mass ϕ.invZ ϕ.pays_mass ϕ.positive D' R hρ
   obtain ⟨C₀,C₁,C₂,C₃,hC,hD,hE,hG,hZ⟩:= hF R V.originBill.f V.aperture V.shelter hρ V.originBill.ease V.wing V.head V.originBill.const V.originBill.letters V.growth
   let u t := Xw.conjCost Y₁.order (Trio.fence Zp (radiusB t) (0:Stars))* Archival.fee k Y₁.order m |C₃ t| m
   have hev : Geo G L₁ u:= (Xw.presold («L»:=L₁) Zp).times (Archival.accepts hG.mean m)
   obtain ⟨T₃,h₃,hT⟩:= lined (k:=k) (j:=Y₁.order) (w:=m) (p:=S.inRank) (q:=T.inMark) (a:=T.outMark) X'.s r X'.u u t₃ X'.wings hr X'.spans hev hx₃
   let Pw: Vale G L₁ (Y₁.order+1):= ⟨Xw,R,hρ,C₀,C₁,C₂,C₃,hC,hD,hE,hG⟩
   have hL : Geo G L₁ (fun t=>(Trio.base Zp (radiusB t):ℝ)):= Geo.basic (Trio.rows G L₁ Zp).2.2.1
   obtain ⟨Yw,hw,hrw,hM⟩:= Estates.office G _ J _ ϕ.roi (Y₁.supportExponent+2) (Trio.coverTicket Zp) (fun t=> Trio.base Zp (radiusB t)) hL ϕ.revenue hΩ.2.1
   let Yx:=Fiord.fuel Zp k m S.inRank T.inMark T.outMark L₁ X'.s T₃ r ϕ.roi X'.u Y₁
   have hp : Geo G L₁ Yx:= Fiord.wages Zp k m S.inRank T.inMark T.outMark _ _ X'.s T₃ r ϕ.roi X'.u Y₁ h₃ X'.wings hr X'.spans ϕ.revenue
   have hh:= hp.joins (show Geo G L₁ (fun x=> Fiord.missCost k (ϕ.roi x)) from ((Geo.fixed 2).times (ϕ.revenue.mean.times (Geo.fixed _))).joins (Geo.fixed 1))
   have hG := moatF η (fun x=> Yx x+_) _ _ _ (k+1) _ hη hh ϕ.progress hw ϕ.positive
   have ht: ∀ᶠ t in atTop, Glass P U Z i j k m hi k' ϕ X₀ r hr D' T₀ T₁ T₂ T₃ Yw η t := by
     filter_upwards [eventually_ge_atTop (Real.exp 1),hR,hM,hG,hJ,hS] with s hs hR hM hG hJ hS
     refine ⟨hS,Kraal.Stereo.Board.remit («X₂»:=t₃) hJ (hT s|>.1),hs,fun β hb=>?_,hM⟩; obtain ⟨h',hv,hh,h₀,h₁,h₂,h₃⟩:= hR β hb
     exact ⟨h',hv,hh,h₀,h₁,h₂,h₃,hG β h' hb.1⟩
   have hh' : ∀ᶠ t in atTop, Cliffe P U Z i j k m hi k' ϕ X₀ r hr D' Pw T₃ t:=by
     filter_upwards [hZ,hf',ht] with x hx he hs
     exact ⟨fun β hb=> let hh := hs.franchises β hb; he β hb.1 hh.1 hh.2.1 hh.2.2.1,hx,(hT x).2⟩

   have hm': Geo G L₁ (fun x=> ϕ.mass x/((m:ℝ)+1)):= by simp only [div_eq_mul_inv]; exact Geo.times ϕ.pays_mass (Geo.fixed _)
   have hD':Geo G L₁ (fun t=> wick G (D.L j) D' t):= (Geo.fixed _).times Geo.by_delay
   have hV' := Sensor.handy G (X₀.tables Y₂.clip (A)) n L₁ S.stencil T.inMark X₀.Z Y₂.supportExponent η hρ (Geo.basic (Trio.circles G _ Zp)) hD' hm' hη
   obtain ⟨y,hy⟩:= eventually_atTop.mp (ht.and (hh'.and hV')); exact ⟨Trio.maxFixed Zp,(eventually_ge_atTop y).mono fun x hx w hw'=> ⟨⟨k',hw',ϕ,X₀,D',hd,r,hr,T₀,T₁,T₂,T₃,h₀,h₁,h₂,h₃,Yw,hrw,hw,fun t ht=> (hy _ (hx.trans ht)).1,Pw,fun t ht => (hy _ (hx.trans ht)).2.1, fun t ht=> (hy _ (hx.trans ht)).2.2⟩⟩⟩
end Holdings
end YM.RGComparison01.Pledge
