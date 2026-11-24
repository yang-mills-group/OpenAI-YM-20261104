import YM.AllOrder.Horizon.Fair
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
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} (A : Alloy X D) (F: Factor A) {c f : Side} {m n N : ℕ}
local notation "a" => A.B.a
local notation "J" => (A.B.a.clock.J (m+1))
local notation "I" => (A.B.a.clock.J m)
local notation "L" => (D.L J)
local notation "x₀" => (A.B.a.clock.hatBeta m)
local notation "z" => betaF G x₀ L
local notation "V" => A.B.a.budget m
local notation "P" => (F.target J I)
local notation "R" => F.shape
local notation "Ω" => (F.expense J I)
local notation "B" => radiusB x₀
set_option quotPrecheck false
local notation "W" => (A.B.a.params m).clip
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "E" => X.p.profile I
local notation "u" => (tall I)
local notation "Y" => (parking u (P).halo)
local notation "d" => (Meadow.studio Y B)

variable (H : Lodge D F.shape (fun _ i=> edgeW i) A.delay)
variable {β : ℝ} (π:f.val=c.val*(A.B.a.S.block m).val) {U:RG.Rep G f} (Z': Chartlet F.shape A N m π U) (hz:SeekR F.shape A N m π Z') (hm:m<N)
local notation "S'" => Pane.panel A m π
local notation "Σ₀" => orchestra A N π
local notation "V₁" => (A.B.a.budget (m+1))
local notation "χ" => Chi.canonical
local notation "Y₀" => (F.shape.o J I|>.K)
variable (hF : Fair D F.target A.delay)
local notation "e'" => Trio.base Y B
local notation "R₀" => strands u (steady Z' u k)
local notation "A'" => (z ^ air I)
local notation "g₀" => gold G L x₀
local notation "g'" => seam_hat I
local notation "κ" => (gainC G L E Y I)
-- fuzzy stencil at actual P, n. Relative to independently defined script + prescribed lower classical and determinant. compare to whole sum on small torus (with Ω removed inside `off`). 
open YM.AllOrder.Local.Pure
variable (r:ℕ)
noncomputable def baseRead (β:ℝ) (K:Forest (Pane.panel A m π).ratio) (ρ:Bid.Dir G c→AxisChart G K) (l:(S').Choices) (x:Positions (Uniform.Primary c G)) := Local.Pure.script K Σ₀ X.O ρ β l r x+ β*Precision.mainTerm (Σ₀).low (Σ₀).down (actual x)+draft γ (Σ₀).down (Σ₀).low (tint G _ x) -- signs

def Mantra (π:f.val=c.val*(A.B.a.S.block m).val) (U:ℝ) (f₀:Offer G c): Prop := let T:= Pane.orchestra A N π
   (∀ i,(V).Regular univ (f₀ i))∧ ∀ (K:Forest (Pane.panel A m π).ratio) (ρ: Bid.Dir G c→AxisChart G K) (l:(Pane.panel A m π).Choices), Critical (S:=Pane.panel A m π) K T.high T.up ρ →
   ∀ x:Positions (Uniform.Primary c G), ‖x‖+2*furl G L x₀ < A' → actual x∈ sunny V→ Brush (E).order (z ^ output r (edgeW I)) (A')⁻¹ (Shellac.off (baseRead A (N:=N) (m:=m) π r U K ρ l+ Trio.froth f₀ ∘ actual)) x

include hm H hF hz
set_option maxHeartbeats 200000 in
lemma emerald (K: Forest (Pane.panel A m π).ratio) (hU:U=virgin (Pane.orchestra A N π) (A.B.a.budget (m+1)) β) (hf:c.val ≤ most Y x₀) {k:ℕ} (hr:r ≤ I)
    (he:Meadow.Budget (V) (Beam.marquee Z' V).reg (High.leftover (strands (tall I) (steady Z' u k)) O k γ|>.logRead) (z ^ g')) (x:Positions (Uniform.Primary c G)) (hp:flags (Pressure.temp x₀) (actual x)=∅) (hq : ‖x‖+2*furl G L x₀ < A') (f₀:Offer G c) (H₀: Mantra A r (N:=N) (m:=m) π U.beta f₀):
    ∀ l:List (Directions G c), l.length≤(V).order→ (∀ v∈l,‖v‖≤(V).threshold) → ‖leftDerivs (stillA (Trio.froth (ledgerV A F π Z' k-f₀))) l (actual x)‖ ≤ ticket (V).order (κ r x₀)+2*((Fintype.card (Site c):ℝ)*(z^ g')) := by -- order?
  subst U
  obtain ⟨hr',h',hzo,hN,hD⟩:= hF _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  obtain ⟨ρ,hρ,hK,hT⟩:= desk (K:=K) A F H π Z' hm rfl hf
  let K':= Classical.arbitrary ((S').Choices); let y:=A'
  have hj:(V).order=(E).order:= congr_arg RG.Stage.order (params_eq A.B.valid m)
  obtain ⟨hv,hi⟩:= weight A F π hm Z' hz K
  have hh : (V).threshold ≤ 2*Pressure.fiery G x₀ L:=by rw [← Z'.laws.data.funds.length_eq]; exact Z'.laws.data.room.temperatures
  let f:=ledgerV A F π Z' k; let q:=Trio.froth (f-f₀); let v:= Trio.froth f₀; let u':= Trio.froth f; have hu':q=u'-v:= by unfold q u' v froth; ext1 k; simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  let f' := Token.arrayE Σ₀ V₁ β γ + v
  have hH : (V).Regular univ q:= by
    rw [hu']; refine CouplingShape.reg_sub ?_ ?_; · rw [show u'=∑ i,f i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> CouplingShape.reg_extend (palaces A F H π Z' hz hm k i) (subset_univ _)
    rw [show v= ∑ i,f₀ i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> H₀.1 i
  intro l hl hw; rw [hj]; apply hD _ rfl hh hj c x hq hp _ _ q f' _ _ (Song.weighty Z' O K* (Fintype.card (Site c):ℝ)) he hH ?_ ?_ l hl hw
  · intro x' hi'; have he':= chants (k:=k) (strands u (steady Z' u k)) _ _ hv x' rfl (hi x') (A.B.support.cap N _ hm.le) (smoky hi'); change Token.arrayE Σ₀ V₁ β γ x'+ v x'= (weighty Z' O K * ↑(Fintype.card (Site c))) -q x' -Boulevard.throng _ x'; rw [he',hu']; change _-u' x'-_ + v x'= _ -(u' x'-v x') - ∑' i,_; ring -- thrust e β
  have hβ:= Z'.laws.intake; have he' : 1<z:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact A.B.a.fits.delayed _; -- positivity
  have hm' :0<furl G L x₀ := Real.rpow_pos_of_pos (zero_lt_one.trans he') _
  have h₁:= lamp G L (zero_lt_one.trans he') β (Z'.laws.data.funds.length_eq ▸ hβ.window.1)
  let f'' := Token.pures (Σ₀) V₁ β - Local.Pure.script K Σ₀ X.O ρ β K' r
  let t := z^edgeW I*(z*y^(r+3)+y^(r+1))+ z^g'
  have ht x (he : ‖(x:Positions (Uniform.Primary c G))‖+2*furl G L x₀<y) (hx:flags (V).threshold (actual x) = ∅) : Brush (E).order t y⁻¹ f'' x:= by
     refine ((hT r x hr hx (he.trans hr') K' y (max_le ?_ ?_) hr').2).smaller (show (E).order ≤ (E).order+I+3 from (by omega))
     · change ‖gStep β‖≤_; rw [Real.norm_of_nonneg h₁.1.le]; exact h₁.2.trans h'
     change ‖x‖≤_; exact le_trans (le_add_of_nonneg_right (by positivity)) he.le
  intro x' he hV
  have h00:‖(0:Positions (Uniform.Primary c G))‖+2*furl G L x₀ < y:= (add_le_add (norm_zero.trans_le (norm_nonneg x)) le_rfl).trans_lt hq
  have ht0 := ht _ h00 (by simp only [actual,map_zero,link_one]; exact smoky («P»:=V) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using (V).threshold_pos))
  have htx:=ht _ he (smoky hV); have hp:= htx.separating ((Brush.certified ht0.pos _).climb ht0.bound le_rfl); have heq : (stillA f') ∘ actual= fun i => (f'' i-f'' 0)+ Shellac.off (baseRead A (N:=N) (m:=m) π r β K ρ K' + v∘ actual) i:= by
    funext i; change f' (actual i)-f' 1=(f'' i-f'' 0)+_
    rw [← (show (actual (0:Positions (Uniform.Primary c G)))=1 from by simp [actual])]; unfold Shellac.off f' f'' baseRead; simp only [Pi.sub_apply,Pi.add_apply,Function.comp_apply]; rw [(show ∀ y:Positions (Uniform.Primary c G),Token.arrayE Σ₀ V₁ β γ (actual y)=_ from fun y=> Token.lines (Σ₀) (V₁) β γ y) i]; simp_rw [(show Token.arrayE Σ₀ V₁ β γ (actual (0:Positions (Uniform.Primary c G)))= _ from Token.lines Σ₀ V₁ β γ 0)]; abel
  rw [heq]; have h':= hp.gathering (H₀.2 K ρ K' hρ x' he hV); apply h'.climb _ le_rfl
  unfold t y gainC; dsimp only; rw [two_mul]
end YM.AllOrder.Shop
