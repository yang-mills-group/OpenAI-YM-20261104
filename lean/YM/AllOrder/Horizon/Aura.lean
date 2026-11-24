import YM.AllOrder.Horizon.Rail
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

variable {η : ℕ→ℕ→ℝ} (H : Lodge D F.shape η A.delay)
variable {β : ℝ} (π:f.val=c.val*(A.B.a.S.block m).val) {U:RG.Rep G f} (Z': Chartlet F.shape A N m π U) (hz:SeekR F.shape A N m π Z') (hm:m<N)
local notation "S'" => Pane.panel A m π
local notation "Σ₀" => orchestra A N π
local notation "V₁" => (A.B.a.budget (m+1))
local notation "χ" => Chi.canonical
local notation "Y₀" => (F.shape.o J I|>.K)
variable (sH: Snow D F.shape A.post A.delay)
    (hϕ : U.path=A.B.kin.path N (m+1)) (he : U.p= A.B.a.budget (m+1)) (hβ: U.beta∈ band A.B.a (m+1)) (hc: 2*Trio.base (parking (tall (A.B.a.clock.J m)) ((F.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo)) (radiusB (A.B.a.clock.hatBeta m))<c.val)
set_option quotPrecheck false
local notation "T0" => Pane.orchestra A N
local notation "Π" => (A.B.a.S.block m)
local notation "d0" => Meadow.studio Y B
local notation "e'" => Trio.base Y B
local notation "t0" => (F.expense J I).wanting
abbrev size_pure:= fence Y B
abbrev clock_pure (i:Stars): (size_pure A F (m:=m) i).val =2*(Trio.tent Y B+i.val):=rfl
local notation "M" => (fence Y B)

abbrev side_pure (i:Stars): (M i*Π).val=(M i).val*(Π).val:=rfl
structure LineCare (N m:ℕ) (A : Alloy X D) (F:Factor A) (t:ℝ) where
   bought (i:Stars) : Chartlet F.shape A N m (Shop.side_pure A F (m:=m) i) (virgin (Pane.orchestra A N (Shop.side_pure A F (m:=m) i)) (A.B.a.budget (m+1)) t)
   seek i : SeekR F.shape A N m _ (bought i)
include F hm
lemma buyings (he:β∈band A.B.a (m+1)): Nonempty (LineCare N m A F β) := by
  choose h hp using fun i:Stars=> Pane.affords A N (Shop.side_pure A F (m:=m) i) hm (Trio.highChair ..|>.2) F.shape F.pledging.conducts.income.grow.1 F.pledging.conducts.full he; exact ⟨⟨h,hp⟩⟩
variable (h : LineCare N m A F U.beta)
abbrev forms (k:ℕ) (i:Stars):= ledgerV A F (side_pure A F i) (h.bought i) k

include hϕ he hc H hm hβ hz
lemma distinct_room :(4*d+16)≤c.val:= by unfold Trio.base Trio.tent at hc; omega
lemma transfer_ready (k:ℕ) : Trio.CompatibleP V d (ledgerV A F π Z' k) (forms A F h k):= by
  have hv (i:Stars):= Trio.highChair Y B i
  refine ⟨fun _=>High.turns _ _ _ _,fun i j=> afloat A F H (side_pure A F i) (h.bought i) hm (side_pure A F j) (h.bought j) rfl rfl rfl rfl hβ rfl k (hv i).1 (hv j).1, fun i=> afloat A F H (side_pure A F i) (h.bought i) hm π Z' rfl hϕ rfl he hβ rfl k (hv i).1 (distinct_room A F H π Z' hz hm hϕ he hβ hc),fun i=> (palaces A F H π Z' hz hm k i).sites⟩ -- arg holes
include h
lemma forms_reg i j k : (V).Regular univ (forms A F h k i j):= CouplingShape.reg_extend (palaces A F H (side_pure A F i) (h.bought i) (h.seek i) hm k j) (subset_univ _)
local notation "ψ" => forms A F h
local notation "Q0" => (clock_pure A F (m:=m))
local notation "g₀" => gold G L x₀
omit hϕ he hc hβ hz
lemma young_azure (sH: Snow D F.shape A.post A.delay) : ∀ᶠ k:ℕ in atTop,∀ (i:Stars) (x:Positions (Uniform.Primary (M i) G)), flags (V).threshold (actual x)=∅ → ‖x‖+2*furl G L x₀<eaves G L x₀ → ∀ l:List (Directions G _), List.length l ≤ (V).order → (∀ k∈l, ‖k‖ ≤ (V).threshold) → ‖leftDerivs (stillA (froth (forms A F h k i))) l (actual x)‖ ≤ crestFeat G L Y E x₀ i:= by
  apply eventually_all.mpr; intro i
  let Z:=h.bought i; have he:=skirt A F H (side_pure A F i) hm Z (h.seek i) (fun _=>rfl); filter_upwards [he] with k he x hv hΩ l hp hh'; have ht:= (Trio.highChair Y B i).2
  let K:= Classical.choice (Tree.select (Pane.panel A m (side_pure A F i)).ratio (Pane.panel A m (side_pure A F i)).patch.odd_side)
  have hQ: Stores.till x₀ ≤ (M i).val:= by unfold Stores.till; omega
  refine le_trans (azure' A F H (side_pure A F i) Z (h.seek i) hm sH K rfl (Trio.taller ..) hQ he x hv hΩ l hp hh') ?_; have hm: turnFee V=Height.away E:= (Rain.jersey (A:=A) (m:=m)).2.2.2
  unfold Trio.crestFeat; rw [(Rain.jersey (A:=A) (m:=m)).1]; have hp := (gold_lit A (m:=m)|>.1); apply add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)) (by norm_num)); rw [← hm]; exact (gold_lit A (m:=m)|>.2).trans (le_add_of_nonneg_left (mul_nonneg (turnFee_pos _|>.le) (add_nonneg hp.le hp.le)))

include hϕ he hc hβ hz sH
lemma polar_reg (x:Site c) (k:ℕ) : (V).Regular (neighbors e' x) (Trio.ornament Q0 (forms A F h k) x):=by
  rw [orchard]; let p i:= Boulevard.stillA (Trio.froth (forms A F h k i))
  have hh i:(V).Regular univ (p i):= by
    have hx : (V).Regular univ (froth (forms A F h k i)):= by rw [show froth (forms A F h k i)=∑ j,(ψ k i) j from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _ => Shop.forms_reg A F H π Z' hz hm hϕ he hβ hc h i j k -- order
    exact CouplingShape.reg_sub hx (CouplingShape.reg_const _)
  have hz i (j:Site (M i)): separation x (Slide.sites (pad Q0 i) x j)≤ e':= (Slide.village (C:=M i) (w:=tent Y B+i.val) (Q0 i).ge _ _).trans (by have hk := i.isLt; unfold Trio.base; omega)
  exact Meadow.regularA _ fun i _=> CouplingShape.reg_scale _ (Slide.regular (pad Q0 i) x (hh i) fun j=> (neighbors_mem ..).2 (hz i j))

lemma polarized : ∀ᶠ k in atTop, ∀ i:Site c,(V).supBounds i (neighbors e' i) (Trio.ornament Q0 (forms A F h k) i) (planks G L Y E x₀):= by
  let Hs:= sH _ _ (A.B.valid.pays m) I (step_paid A.B.a m) |>.2.2.2
  let B':= V; obtain ⟨hzF,hp,hV,hΨ⟩:= Rain.jersey (A:=A) (m:=m); let f:= crestFeat G L Y E x₀
  have he' i:0 ≤ f i:= by unfold f crestFeat Boulevard.ticket; rw [← hΨ]; have hn:=turnFee_pos B'; have hg:= gold_lit A (m:=m)|>.1; unfold B' at hn; positivity
  rw [← (Trio.loses G L Y E x₀ B' hzF hp).2]
  have hO : B'.threshold ≤2*Pressure.fiery G x₀ L:= by have ht:= Z'.laws.data; rw [← ht.funds.length_eq]; exact ht.room.temperatures
  filter_upwards [young_azure A F H hm h sH] with k hk x
  apply Trio.kinds _ _ _ _ (forms_reg A F H π Z' hz hm hϕ he hβ hc h (k:=k)) he' (by unfold Trio.base; omega) (Sienna.furl G L x₀) (eaves G L x₀) x ?_ hk -- forms_reg binders
  intro U hU i; apply Hs B' hO _ _ hc (Trio.tent Y B+i.val) (show Trio.tent Y B +i.val+1≤ e' from (by unfold Trio.base; have hi:=i.isLt; omega)) (clock_pure A F i).ge x U hU
end YM.AllOrder.Shop

