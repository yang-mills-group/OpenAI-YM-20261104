import YM.AllOrder.Horizon.Ahead
set_option autoImplicit false
noncomputable section
/-! # Pointwise full density pass to post-Mark E6 cabinet after alignment and tickets. -/
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

variable (H : Lodge D F.shape (fun _ i=> Shop.edgeW i) A.delay)
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
variable (h : LineCare N m A F U.beta) {k:ℕ}
local notation "Yd" => Shop.forms A F h k
local notation "R0" => strands u (steady Z' u k)
local notation "G0" => (clock_pure A F (m:=m))
local notation "E0" => H
local notation "W0" => Time.forecastK A.B.a m F.scout U.beta
open Marlin Progress.DirectedRecipe Payments

local notation "M" => Shop.size_pure A F (m:=m)

variable (hF: Fair D F.target A.delay)
include hF hm hϕ he H hc hβ hz
lemma thin_shadow (r:ℕ) (hr:r ≤ I) (Lad: ∀ i:Stars, Offer G (M i)) (hh:∀ i:Stars, Shop.Mantra A r (N:=N) (side_pure A F i) U.beta (Lad i)) (hg: ∀ i:Stars, let Yx:= h.bought i; Meadow.Budget V (Beam.marquee Yx V).reg
  (Shop.present A F (side_pure A F i) Yx k|>.logRead) (z ^ seam_hat I)):
    Meadow.Budget V (Marlin.leap (c:=c) e') (mirrored A F h k-Trio.ornament G0 Lad) (z ^ output r (4*edgeW I)) := by
  let T (i:Stars) : Offer G (M i):= (forms A F h k i) - Lad i; let f:=creditC G L E Y I r x₀; let c':=priceC G L E Y I r x₀
  let P':= V
  have he i j: P'.Regular univ (T i j):= CouplingShape.reg_sub (forms_reg A F H π Z' hz hm hϕ he hβ hc h i j k) ((hh i).1 j)
  obtain ⟨hℓ,hp,hV,_⟩:= Rain.jersey (A:=A) (m:=m)
  have ht:= hF _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have hcT T':0 < z ^ (T':ℝ):= Real.rpow_pos_of_pos (by rw [← PriceCompiler.beta_eq A.B.valid]; exact zero_lt_one.trans (A.B.a.fits.delayed _)) _
  have hz':1<z:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact A.B.a.fits.delayed _
  have hf i: 0≤ f i:= by unfold f creditC Boulevard.ticket gainC; dsimp only; positivity
  let y:=z^ air I
  have hf' : P'.threshold ≤2*Pressure.fiery G x₀ L:= by have ht:= Z'.laws.data; rw [← ht.funds.length_eq]; exact ht.room.temperatures
  let w:=e'; have hw : Trio.tent Y B+4≤w:= by unfold w Trio.base; omega
  have h₁ (i:Site c): P'.supBounds i (neighbors e' i) (ornament G0 T i) c':= by
    have hcost: c'=Trio.oroW P' e' f:= by unfold c' Trio.oroW Trio.tilt priceC; rw [hp,hℓ]
    rw [hcost]; apply Trio.kinds V G0 e' T he hf hw (Sienna.furl G L x₀) y i
    · intro U hU j; exact ht.2.2.2.1 P' hf' _ _ hc _ (show Trio.tent Y B+j.val+1≤w from (by unfold w Trio.base; have hx:=j.isLt; omega)) (clock_pure A F j).ge i U hU
    intro j P0 hp hk l hl hL; have hv:=side_pure A F (m:=m) j; have hB:= emerald A F H hv (h.bought j) (h.seek j) hm hF r (Classical.choice (Tree.select (Pane.panel A m hv).ratio (Pane.panel A m hv).patch.odd_side)) rfl (Trio.taller ..) hr (hg j) P0 hp hk _ (hh j) l hl hL
    rw [hℓ] at hB; exact hB
  have hK : ∀ i:Site c,P'.Regular (neighbors e' i) (ornament G0 T i):= by
    -- from polar_reg
    intro x; rw [orchard]
    have hz i (j:Site (M i)): separation x (Slide.sites (pad G0 i) x j)≤ e':= (Slide.village (C:=M i) (w:=tent Y B+i.val) (G0 i).ge _ _).trans (by have hk := i.isLt; unfold Trio.base; omega)
    have hh (i:Stars): P'.Regular Finset.univ (Boulevard.stillA (Trio.froth (T i))):= by
      apply CouplingShape.reg_sub _ (CouplingShape.reg_const _); rw [show froth (T i)=∑ j,T i j from funext fun x=>(Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> he _ _
    exact Meadow.regularA _ fun i _=> CouplingShape.reg_scale _ (Slide.regular (pad G0 i) x (hh i) fun j=> (neighbors_mem ..).2 (hz i j))
  have he': mirrored (c:=c) A F h k - ornament G0 Lad= Trio.ornament G0 T:= by
    funext y x; change ornament G0 Yd y x-ornament G0 Lad y x= _; simp only [orchard,Finset.sum_apply,← Finset.sum_sub_distrib]; apply sum_congr rfl; intro i hi; dsimp only [Function.comp_apply, Pi.smul_apply]; rw [← smul_sub]; congr 1; unfold stillA froth T; simp only [Pi.sub_apply,sum_sub_distrib]; ring
  rw [he']; refine ⟨fun _=>c',fun i=> ?_,fun i=>⟨hK i,h₁ i⟩⟩; apply budget_finite
  · intro i; split; exact mul_nonneg ((h₁ 0).1) (Real.exp_pos _).le; rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (leap e' i).site=i from rfl)]
  · apply le_trans _ (ht.2.2.1 r hr); rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ ((h₁ i).1); apply Real.exp_monotone; have hh: preExponent P' = Trio.stout E:=by unfold preExponent Trio.stout; rw [hV]
    rw [← hh]; apply mul_le_mul_of_nonneg_left _ (headline V|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters Y (radiusB x₀) (V).B_pos i e' (by omega)).trans; rw [two_mul]
  · intro j hj he; exact if_neg he
  simp

/- CP2 local consumer: full answer as exact relocalized kernel. `he` is the
PURE input or another presentation with E=0 and path/s data **still** from the
real family; `K` forced entries with qualifications unrestricted. Includes
φ, σ Prelude & weight bills before merge. Empty Mantra not ruled out yet through
positive orders. Later k-order model estimates in terms of the independent
`desk` on the aux periods (on its shape at a permitted radius) will let us use
the penultimate clause. -/
include sH
abbrev armor_cap := planks G L Y E x₀
local notation "γ0" => z ^ seam_hat I
local notation "s'" => planks G L Y E x₀
structure HasLedger (k:ℕ) : Prop where
   safety i : Tidy (V) (neighbors (2*e') i) (indicator A F π Z' h k i) ∧ (∀ U,indicator A F π Z' h k i U≠0 → ¬Healthy (V).threshold (neighbors (2*e') i) U) ∧ ∀ U,‖indicator A F π Z' h k i U‖ ≤ lossFee G L t0 Y E x₀
   collection : Collection.Local (Shop.hotel1 A F π Z') (V) (Shop.roomrise A F π Z' h k) (Time.forecastE A.B.a m) W0
   high : Meadow.Budget V (Shop.hotel A F π Z'|>.reg) (Shop.present A F π Z' k|>.logRead) γ0
   caps i : (V).Regular (neighbors e' i) (Shop.mirrored A F h k (i:Site c)) ∧ (V).supBounds i (neighbors e' i) (Shop.mirrored A F h k i) s'
   ready : CompatibleP V d (ledgerV A F π Z' k) (forms A F h k)
   implies r (hr:r ≤ I) : ∀ Lad: (i:Stars)→ Offer G (M i),(∀ i:Stars, Shop.Mantra A r (N:=N) (side_pure A F i) U.beta (Lad i)) → Meadow.Budget V (Marlin.leap (c:=c) e') (Shop.mirrored A F h k - Trio.ornament G0 Lad) (z ^ output r (4*edgeW I))
   pushed K (v:Config G c) : (S').push U.beta U.eval v=earlyValue (hotel1 A F π Z') (T0 π).down (T0 π).low V (roomrise A F π Z' h k) U.beta (Song.weighty Z' O K-ledgerV A F π Z' k 0 1) γ v
lemma fit (hv:∀ i,U.activities.E i=0) : ∀ᶠ k in atTop, HasLedger A F π Z' h k:= by
  have h₁ := skirt A F H π hm Z' hz hv
  have hh : ∀ i:Stars, ∀ᶠ k in atTop, Meadow.Budget (V) ((Shop.hotel A F (side_pure A F i) (h.bought i)).reg) ((Shop.present A F (side_pure A F i) (h.bought i) k).logRead) γ0:= fun i=> skirt A F H (side_pure A F i) hm (h.bought i) (h.seek i) (fun _=>rfl)
  filter_upwards [h₁,eventually_all.mpr hh,Shop.polarized A F H π Z' hz hm sH hϕ he hβ hc h] with k hs h₀ hA
  exact ⟨safety_bill A F H π Z' hz hm sH hϕ he hβ hc h k,balanceE A F H π Z' hz hm sH hϕ he hβ hc h k hs hA, hs,fun i=> ⟨Shop.polar_reg A F H π Z' hz hm sH hϕ he hβ hc h i k,hA i⟩, transfer_ready A F H π Z' hz hm hϕ he hβ hc h k,fun r hr x hx=> thin_shadow A F H π Z' hz hm hϕ he hβ hc h hF r hr x hx h₀, fun K x=>realize A F H π Z' hz hm sH hϕ he hβ hc h k K hs x⟩
end YM.AllOrder.Shop
