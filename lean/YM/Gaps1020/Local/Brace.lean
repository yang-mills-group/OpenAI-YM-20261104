import YM.Gaps1020.Local.Align
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Renew
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time Rain Mallow Roost UVNext.CouplingReset Daisy.Charity.RG12
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open YM.ConnectedActivityE6.Blaze.Thermal1020
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
variable {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A} {c f L:Side} {m n N ℓ i k d M:ℕ}{l s:ℝ}
variable {Y: UVNext.CouplingReset.In A.B.a m n} (H: Spring R N m n l s Y)(x:Set.Icc l s)
local notation "i0" => A.B.a.clock.J (m+1)
local notation "j0" => A.B.a.clock.J m
local notation "O" => Chi.canonical
local notation "P₀"=> A.B.a.budget m
local notation "Tᴹ" M:max => (fun p:ℕ=> M + 1 ≤ p)
local notation "x₀"=> A.B.a.clock.hatBeta m
local notation "φ"=> A.B.kin.alpha N m
local notation "V₀"=> Y x.val
local notation "W"=> H.H
local notation "E0" => H.H.base
local notation "X0"=> H.H.sister x
local notation "S0"=> Mallow.houseS H x
local notation "C0" => A.B.a.S.side m n
local notation "L0"=> D.L i0
local notation "Γ"=> R.expense i0 j0
local notation "Z"=> Thermal1020.horizonRadius G L0 x₀
variable (h:m<N) (he: Mallow.RG12.Earned (Thermal1020.Shared.markerBudget G) R.shape A.delay) (hM:M ≤ A.B.a.clock.J (m+1))
local notation "ℓ₀" => turnFee P₀
local notation "Δ" => ℓ₀ * ((Z^(M+1))⁻¹)
local notation "d'"=> H.ordinal
local notation "V'" i=> Rain.moor R.target A m i
local notation "Z0"=> screens R.target A m
local notation "wid"=> Rain.lint R.target A m
local notation "e"=> Trio.base wid (radiusB x₀)

set_option quotPrecheck false
local notation "pX"=>opening W
local notation "X!"=> (paint W H.knows H.W H.ordinal x.val)
local notation "F'"=>Magazine E0→ Config G C0→ℝ
local notation "hg1"=> (plusone E0 X0 O φ).hardRead
local notation "P'"=> Beam.marquee E0 P₀
local notation "k1" => (Cash.armK (R.target i0 j0) L0 (R.shape.μ i0 j0) x₀ 0 (R.expense i0 j0).degrees)
local notation "k0" => (forecastK A.B.a m R.scout (Y x.val).beta)

local notation "p0" => quota A m M
local notation "p1" => demand A wid m p0
local notation "P₁"=> A.B.kin.path N m
local notation "v1"=> H.result x
local notation "V1"=> (v1).activities
local notation "Φ" a:max => Averaging.delta ((pX).read a)
local notation "Ψ" I:max x:max => coverWorld V1 pX P₀ P₁ (A.B.a.params m).clip I x
local notation "Y0"=> A.B.a.clock.allowance m
local notation "D'"=> A.B.a.clock.forcedAllowance m
-- map from actual frame. low has K exact. target output quantities
variable (M) (hG:G.Simple)
def proposed := Ψ (paintLow H x M) φ
def ignored := Ψ (earnest H x M) 0
abbrev betaLow:= predictor A.B N Y x + Φ (paintLow H x M)
-- scalar **including** log kernel/vac from H.τ. Exact nonprincipal
-- pref from same geometry winding. Compare scalar per site, not claim
-- Hessian/moves V-analytic already clustering of period measure.
def scalarPlan :=Collection.vac (paintLow H x M) (Embrasure.payment W H.O x - barLow H x M)

section verify
include h he hM hG
local notation "F0" => (paintLow H x M)
local notation "D0" => (earnest H x M)
local notation "E'" => (ignored M H x)
local notation "F₀" => (proposed M H x)
local notation "σ₀"=> (A.B.a.budget m).threshold
local notation "sf"=> Time.base G (A.B.a.params m)
private lemma hypothesisY : (V1).E=(F₀).E+(E').E:=by
   let B:= P₀; obtain ⟨hL,hH⟩:= prePartials M H x h he hM; have hw:= H.core h _ x.property
   unfold proposed ignored
   rw [H.owns hG h x.property]; exact alignment hG _ (statement M H x) hw hH hL
private lemma actualβ : let d:=Φ D0; (v1).beta= betaLow M H x+d ∧ σ₀^2*|d| ≤ p1:=by
   let B:= P₀; obtain ⟨hL,hH⟩:= prePartials M H x h he hM; have hw:= H.core h _ x.property
   have hU:= delta_split hG (statement M H x) hw hH hL
   intro d; refine ⟨?_,Averaging.delta_bound hG hL.projects⟩; rw [H.owns hG h x.property]; change predictor A.B N Y x.val + Φ X! = betaLow M H x + d; exact (congr_arg ((predictor A.B N Y x.val)+·) hU).trans (add_assoc ..).symm
omit hM he in
private lemma is_post (α v0 u)(hl:Collection.Local (pX) P₀ u v0 k0) : let P:= A.B.a.params m; (Ψ u α).Valid P₀ (regularNeed G P₀ P.clip P.width P.paths α v0) D' := by
   intro P
   have hp:= (R.machine.passes h H.knows).1
   have hv := (H.moves hG h|>.2 x x.property|>.1).bundle
   have ht:(V1).Valid P₀ Y0 D':= hv.valid.labels
   have hf: (V1).reg=(drawer G C0).reg:= by rw [H.owns hG h x.property]; rfl
   exact pasted hG V1 (Ψ u α) hl ht hf (A.B.support.cap N m h.le) hp.decent hp.width (Return.enough_room A.B m n) α rfl
lemma neglected : (E').Valid P₀ (sf*p1) D':= by
   let B:=P₀; let P:=A.B.a.params m
   have hy : regularNeed G B P.clip P.width P.paths 0 p1= sf*p1 := by rw [Time.table G P ⟨rfl,rfl,rfl⟩,abs_zero,zero_mul,mul_zero, add_zero]
   rw [← hy]; exact is_post H x h hG 0 p1 D0 (prePartials M H x h he hM).1
lemma admissibleLow : let B:=P₀; let P:=A.B.a.params m; (F₀).Valid P₀ (regularNeed G B P.clip P.width P.paths φ (forecastE A.B.a m+p1)) D':= by
   intro B P; exact is_post H x h hG φ (forecastE A.B.a m + p1) F0 (prePartials M H x h he hM).2
omit h he hM hG in
private lemma resize {X Y Z1:Activities G c}{B a b h w} (hx:X.E=Y.E+Z1.E)(hh:X.reg=Y.reg)(h':Z1.reg=Y.reg)(he:X.Valid B a w)(hf:Z1.Valid B b w)(hg:Y.Valid B h w): Y.Valid B (a+b) w:= ⟨hg.regular,hg.forced,hg.moves,eBudgetSub X Z1 Y hh h' hx he hf,hg.boundK⟩
lemma adapt :
     (F₀).Valid P₀ (Y0+sf*p1) D' ∧ (E').Valid P₀ (sf*p1) D' ∧
     (V1).E=(F₀).E+(E').E ∧
     let d:=Φ D0
     (v1).beta= betaLow M H x + d ∧ σ₀^2 * |d| ≤ p1:=by
   have he' := hypothesisY M H x h he hM hG; have hY := neglected M H x h he hM hG
   have hr : (F₀).reg=(V1).reg:= by unfold proposed coverWorld; rfl
   have hx : (E').reg=(V1).reg:= by unfold ignored coverWorld; rfl
   refine ⟨resize he' hr.symm (hx.trans hr.symm) ?_ hY (admissibleLow M H x h he hM hG), hY, he', actualβ M H x h he hM hG⟩
   exact (H.moves hG h|>.2 x x.property|>.1.bundle).valid.labels
-- physical target division scalar split. Keep formula on same label reading. global cost compensated exactly via /card
local notation "σd"=> (Meadow.studio wid (radiusB x₀))
local notation "zf"=> (ballCost σd:ℝ)
private abbrev pathP: Match.Alliance S0 S0 1 0:= Match.staple rfl rfl rfl
omit H x h hG he hM in
private lemma uniformBudget {X:Listing G c}{B:BudgetPoint}{W':Collection.Source G c}{w a:ℝ}(h: Collection.Local X B W' w a): let f:=fun i=>W'.logRead i 1; Summable f ∧ ‖∑' i,f i‖ ≤ (Fintype.card (Site c):ℝ)*w:= by
   intro f
   obtain ⟨z,hz,hT⟩:= h.cheap; have hg:= Boulevard.planetary hT (fun i=> (hz i).1); have ht(i): ‖f i‖ ≤ z i:=by
       let Y:=(X.reg i).support
       have hV: Healthy B.threshold Y (1:Config G c):= by unfold Healthy; rw [smoky («P»:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos)]; simp
       exact (hz i).2 _ hV [] (by simp) (by simp)
   have hx':= budget_mono hg (fun i=> norm_nonneg (f i)) ht; exact ⟨hx'.2.1.of_norm,(norm_tsum_le_tsum_norm hx'.2.1).trans hx'.2.2⟩
lemma priceScalar : |(v1).v - scalarPlan M H x| ≤ p1 + zf *p0:=by
   obtain ⟨hz,hV⟩:= prePartials M H x h he hM; let U:= F₀
   let Y0' := Post.couponSet (pathP H x) (Tᴹ M) M O
   let b:=Post.OfferP.pile d' P₀ S0 Y0' (0:Site C0) 1
   have ho : (Embrasure.payment W H.O x.val-barLow H x M) -b = Rain.stanzaFee W d' H.O x.val:=by
      unfold Rain.stanzaFee; rw [H.H.click (x:=x.val) x.property]; change _= _ - Meadow.barony S0 O d' φ 0 1
      rw [Meadow.aster O P₀ (pathP H x) rfl rfl rfl,Post.composeCurve (M:=M)];
      change _=_ - Post.OfferP.pile _ _ _ (_+_) _ _; rw [Post.OfferP.add]; change _=_-(barLow H x M+b); ring
   let C:= (Fintype.card (Site C0):ℝ); let y:= ∑' i,(D0).logRead i 1
   have hp: (v1).v=Collection.vac X! (Rain.stanzaFee W d' H.O x.val):= (H.moves hG h|>.2 x x.property).2.2.2
   have ht : (v1).v-scalarPlan M H x= -b-y/C:= by
       rw [hp, ← ho, scalarPlan, Collection.vac, Collection.vac]
       have h' i: (X!).logRead i 1=(F0).logRead i 1+(D0).logRead i 1:= by rw [statement]; rfl
       simp_rw [h', Summable.tsum_add ((uniformBudget hV).1) ((uniformBudget hz).1)]; change _- (_+y)/C-(_-_/C)=_; ring
   have ha: ‖b‖ ≤ zf*p0:=by
       have hy:= generalPane (N:=N) h he hM (A.B.a.S.oneStep m n|>.exact_size) _ _ _ _ (pathP H x) (fun _=>True)
       simp only [↓reduceIte] at hy
       exact Post.OfferP.scalar _ _ _ _ hy rfl _ (smoky («P»:=P₀) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using (P₀).threshold_pos))
   have hγ:0<C:=Nat.cast_pos.mpr Fintype.card_pos; have hx' : |y/C| ≤ p1:= by rw [abs_div,abs_of_pos hγ, div_le_iff₀ hγ]; exact (uniformBudget hz).2.trans_eq (mul_comm ..)
   rw [ht]; exact ((abs_sub _ _).trans (add_le_add (abs_neg _ |>.trans_le ha) hx')).trans_eq (add_comm ..)
end verify
end YM.GapsLocal.Renew
