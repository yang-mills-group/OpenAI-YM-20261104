import YM.AllOrder.Horizon.Aura
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
variable (h : LineCare N m A F U.beta) {k:ℕ}
local notation "Yd" => Shop.forms A F h k
local notation "R0" => strands u (steady Z' u k)
local notation "G0" => (clock_pure A F (m:=m))
local notation "E0" => H
local notation "W0" => Time.forecastK A.B.a m F.scout U.beta
open Marlin Progress.DirectedRecipe Payments

def indicator (k:ℕ) := High.occasion (strands u (steady Z' u k)) O V γ G0 e' (forms A F h k) k
def mirrored (k:ℕ) : Offer G c := Trio.ornament G0 (forms A F h k)
def present (k:ℕ) := High.leftover (strands u (steady Z' u k)) O k γ
def passport (k:ℕ) := Marlin.bison (Shop.present A F π Z' k) (mirrored (c:=c) A F h k) (indicator A F π Z' h k)
def hotel := Beam.marquee Z' V
def hotel0 := Marlin.lodge (hotel A F π Z') e' (2*e')
def hotel1 := Marlin.pluck V (hotel0 A F π Z')
def roomrise (k:ℕ) := Marlin.poursP V (hotel0 A F π Z') (passport A F π Z' h k)
abbrev p0:= plusone Z' (Match.staple (H:=Z') («J»:=Z') rfl rfl rfl) O γ

include hϕ he H sH hc hβ hm hz
lemma safety_bill (k:ℕ) (i:Site c) : Tidy (V) (neighbors (2*e') i) (indicator A F π Z' h k i) ∧ (∀ U,indicator A F π Z' h k i U ≠ 0→ ¬Healthy (V).threshold (neighbors (2*e') i) U) ∧
    ∀ U,‖indicator A F π Z' h k i U‖≤ lossFee G L t0 Y E x₀:= by
  let P0:= ledgerV A F π Z' k; let R':= Trio.tent Y B; let w:=e'; let T' := clock_pure A F (m:=m); have hw: R'+4 ≤ w:= by unfold R' w Trio.base; omega
  have ht:2*d ≤ R':= by unfold R' Trio.tent; omega
  have H0:=weight A F π hm Z' hz (Classical.choice (Tree.select (S').ratio (S').patch.odd_side)); have hk:= roomCheck A F H π Z' hz hm k
  have hT:= forms_reg A F H π Z' hz hm hϕ he hβ hc h (k:=k)
  have hcost V':= early_cloud (k:=k) (H:=Z') _ O V γ G0 e' (forms A F h k) V' rfl hk (perimeter ..) i H0.1 (fun _=>Shop.hatchHeat A F (m:=m)) (fun j Vu hv x=> ticket_room A F H (side_pure A F j) (h.bought j) (h.seek j) hm k x Vu hv) hw -- order
  refine ⟨High.tidy_occasion _ O V γ G0 e' (forms A F h k) rfl hk (perimeter ..) i H0.1.smooth hT hw (by omega) le_rfl,fun v hh hv=> hh ?_,fun v=>?_⟩
  · let A':= transfer_ready A F H π Z' hz hm hϕ he hβ hc h k
    exact High.occasion_none _ O V γ G0 e' (forms A F h k) rfl hk (perimeter ..) i le_rfl hw ht (by unfold R' w Trio.base Trio.tent at *; omega) (by unfold Meadow.studio Meadow.roomSize; omega) A' hv
  have hp:= hcost v; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.2] at hp
  exact hp
omit H sH hϕ he hβ hm hz hc
lemma moves (k:ℕ) (s:Signed) (b:Site c) : Nonempty (((hotel A F π Z').read (Shop.present A F π Z' k)).Moves s b):= Beam.moves _ _ O _ s b _

include hϕ he H sH hc hβ hm hz
lemma merget (k:ℕ) : Ingredients (Shop.hotel0 A F π Z') (dummy (Shop.passport A F π Z' h k)) (raiser V) 0 W0 := by
  let v₀:=lossFee G L t0 Y E x₀; let K:=Marlin.tithe (2*e') v₀ V (coverTicket Y)
  have h':0≤ v₀:= (norm_nonneg _).trans ((safety_bill A F H π Z' hz hm sH hϕ he hβ hc h k 0).2.2 1)
  have hK:0≤K:=by unfold K Marlin.tithe; positivity
  have hp:=Rain.jersey (A:=A) (m:=m)
  have hM:(S').kernel=(a).clock.kernel:=rfl; let c':= Cash.armK P L (F.shape.μ J I) x₀ 0 (Ω).degrees
  let v β:=(F.scout J I).pair.strong z β
  have hv : Next.Scheduling.inBand z U.beta := by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hβ
  have heq : W0=v U.beta:= by unfold Time.forecastK; rw [PriceCompiler.beta_eq A.B.valid]
  let Θ := Match.staple (H:=Z') («J»:=Z') rfl rfl rfl
  have ht : (V).supportExponent+3≤ (Ω).earn:= by rw [hp.2.2.1]; exact F.pledging.agenda _ _ (step_paid A.B.a m)|>.1
  have ht': (raiser V).supportExponent+1≤ (Ω).earn:= by change (V).supportExponent+1+1≤_; linarith only [ht]
  obtain ⟨f,hf,hF⟩:= Refrain.chargesOut (raiser V) Z' Θ O hz rfl ht'
  have hC := F.pledging.conducts.income.earns J I (step_paid A.B.a m) x₀ (A.B.valid.pays m) _ hv
  have hv': K ≤ z ^ (-(1/8:ℝ)):= by unfold K Marlin.tithe; rw [hp.2.2.1]; exact (sH _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).1
  rw [heq]
  obtain ⟨b,hg⟩:= (F.inn.terms.allot _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.2.2.1) U.beta hv c' K (budget_nonneg (hF 0)) hK (hC.trans_eq (by ring)) hv' -- close arithmetic
  let Y' := Shop.present A F π Z' k; let H':= Shop.hotel A F π Z'; let v (x:Site c):= indicator A F π Z' h k x; have hY:= safety_bill A F H π Z' hz hm sH hϕ he hβ hc h k
  refine Marlin.stakes V (hotel A F π Z') e' (2*e') (Shop.present A F π Z' k) (mirrored A F h k) (indicator A F π Z' h k) (Refrain.qualified _ _ _ _ _ _ rfl) (Shop.moves A F π Z' k) hg hf hF (fun i=> (hY i).1) (fun i=> (hY i).2.1) (fun i=> (hY i).2.2) ?_ (le_refl K)
  intro i; unfold coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters Y B (V).B_pos i _ le_rfl); rw [two_mul]

abbrev heritage := z ^ seam_hat I
lemma balanceE (k:ℕ) (heB: Meadow.Budget V (hotel A F π Z'|>.reg) (Shop.present A F π Z' k|>.logRead) (z ^ seam_hat I)) (hY : ∀ i:Site c,(V).supBounds i (neighbors e' i) (mirrored A F h k i) (planks G L Y E x₀)) :
    Collection.Local (hotel1 A F π Z') V (roomrise A F π Z' h k) (Time.forecastE A.B.a m) W0:= by
  let B' := V; let b' := planks G L Y E x₀; let s':= b'*Real.exp (preExponent V* coverTicket Y); let H':= Shop.hotel A F π Z'; let G':= mirrored (c:=c) A F h k
  have he' i:= polar_reg A F H π Z' hz hm sH hϕ he hβ hc h i k -- order
  have hv:0≤ b':= (hY 0).1
  have hF: Meadow.Budget V (Marlin.leap e') G' s':= by
    refine ⟨fun _=> b',fun i=> ?_,fun i=>⟨he' i,hY i⟩⟩; apply budget_finite
    · intro i; split; exact mul_nonneg hv (Real.exp_pos _).le; rfl
    rw [Finset.sum_eq_single i]; rw [if_pos (show (leap e' i).site=i from rfl)]
    · apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline V|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters Y (radiusB x₀) (V).B_pos i e' (by omega)).trans; rw [two_mul]
    · intro j hj he; exact if_neg he
    simp
  let U':=Shop.present A F π Z' k; let d':=indicator A F π Z' h k
  have hg:= Marlin.reg_bison H' e' (2*e') U' G' d' heB hF; have hx:= merget A F H π Z' hz hm sH hϕ he hβ hc h k
  have hs:Collection.Local (hotel1 A F π Z') V (roomrise A F π Z' h k) (z^seam_hat I+turnFee V*s') W0:= Marlin.sous hx hg (fun s b=> reeds _ _ _ U' G' d' s b ((moves A F π Z' k s b).some))
  have hΓ: turnFee V=Height.away E:= (Rain.jersey (A:=A) (m:=m)).2.2.2
  have hp : z^seam_hat I+turnFee V*s'≤ Time.forecastE A.B.a m:= by
    let y:=gold G L x₀; let z':= Height.away E
    have hg := gold_lit A (m:=m); let D₁:= Time.forecastE A.B.a m
    have ht' : z'*y+y+z'*s' ≤ (1/2:ℝ)* D₁ := by
      have hj: preExponent V= Trio.stout E:= by unfold preExponent Trio.stout; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]
      unfold s' b' D₁ Time.forecastE; rw [hj,PriceCompiler.params_eq A.B.valid]; exact (sH _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).2.1
    have hv: 0 ≤ D₁:= by unfold D₁ Time.forecastE; apply mul_nonneg (Time.credit_pos .. |>.le); exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
    rw [hΓ]; change _+z'*_≤_; exact (add_le_add hg.2 le_rfl).trans (show y+z'*s'≤ D₁ from (by linarith only [ht', hv,mul_nonneg (show 0≤z' from hΓ ▸ turnFee_pos B' |>.le) (show 0 ≤ y from hg.1.le)]))
  obtain ⟨f,hf,h'⟩:= hs.cheap; exact {hs with cheap:= ⟨f,hf,fun i=>budget_loosen (h' i) hp⟩}

lemma realize (k:ℕ) (K:Forest (S').ratio) (heB : Meadow.Budget V (hotel A F π Z'|>.reg) (Shop.present A F π Z' k|>.logRead) (z ^ seam_hat I))
    (U' : Config G c) : (S').push U.beta U.eval U'= earlyValue (hotel1 A F π Z') (T0 π).down (T0 π).low V (roomrise A F π Z' h k) U.beta (Song.weighty Z' O K-ledgerV A F π Z' k 0 1) γ U':= by
  have hK:= weight A F π hm Z' hz K; refine (hK.2 U').trans ?_; exact Marlin.carries V (hotel A F π Z') e' (2*e') (Shop.present A F π Z' k) (mirrored A F h k) (indicator A F π Z' h k) U' («R»:=posting V Z') (p0 A F π Z') (fun i=>⟨rfl,rfl⟩) _ _ _ _ _ _ (merget A F H π Z' hz hm sH hϕ he hβ hc h k) heB (fun i=> levyG _ _ _ _ _ _ _ _ _ _ hK.1) hK.1.transforms (Shop.moves A F π Z' k)
end YM.AllOrder.Shop
