import YM.AllOrder.Horizon.More
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
variable {k : ℕ}
--- these helpers collect later requests for merger budgets & remainder tickets.
abbrev hatchHeat:= Trio.heat G L (Ω).wanting Y E x₀
abbrev bankrupt:= (turnFee V * (z^(Ω).wanting + z ^ (-(7/16):ℝ)))
abbrev worthFeeP:= (Cash.armK (P) L (F.shape.μ J I) x₀ 0 (Ω).degrees)

local notation "Σp" => (strands (tall I) (steady Z' u k))
local notation "Π" => (A.B.a.S.block m)
local notation "d0" => Meadow.studio Y B
include H hm hz
lemma roomCheck (k:ℕ) : ∀ i∈ strands (tall I) (steady Z' u k), ∀ v∈perf Z' i, perf Z' i⊆ neighbors d v:= by
  intro i hi v hv; apply (High.hall u _ u _ check_steady i ((runIn ..).1 hi) hv).trans; intro z' hz'; have hh:= (neighbors_mem ..).1 hz'; exact (neighbors_mem ..).2 (hh.trans ((Nat.le_add_right ..).trans (traffic u _ B (V).B_pos)))

lemma ticket_room (k:ℕ) (x:Site c) (s:Config G c) (he: flags (V).threshold s=∅): ‖ledgerV A F π Z' k x s‖ ≤ hatchHeat A F (m:=m) := by
  let K:= Classical.choice (Tree.select (Pane.panel A m π).ratio (Pane.panel A m π).patch.odd_side)
  have ht:= chamber_value (k:=k) _ O V γ s rfl (roomCheck A F H π Z' hz hm k) (perimeter ..) x (weight A F π hm Z' hz K).1 he
  rw [Rain.jersey (A:=A) (m:=m)|>.2.2.2] at ht; exact ht
-- forecast ↓old cap for PUre; merge usable with high Claim. using Gold-bound not foliage-aspiration.
variable (sH: Snow D F.shape A.post A.delay)
include sH
omit H hz Z' hm in
lemma permits0 : Pane.Planks D F.shape A.post (most_side D F.target) A.delay (fun _ i=> (X.p.profile i).order):= fun j i hi t ht=> (sH _ _ ht i hi).2.2.1
include sH
omit H hz hm sH in
lemma gold_lit : 0<gold G L x₀ ∧ z^seam_hat I ≤ gold G L x₀ := by
  have hp:1<z:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact A.B.a.fits.delayed _; -- structure warning all variables
  have hi:I≥1:= Nat.le_trans (by norm_num : 1≤4) (A.B.a.clock.adm m)
  exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans hp) _, Real.rpow_le_rpow_of_exponent_le hp.le (show seam_hat I ≤ -(23/20:ℝ) by unfold seam_hat; linarith [Nat.one_le_cast (α:=ℝ)|>.mpr hi])⟩
local notation "g₀" => gold G L x₀

lemma azure' (K: Forest (Pane.panel A m π).ratio) (hU:U=virgin (Pane.orchestra A N π) (A.B.a.budget (m+1)) β) (hf:c.val ≤ most Y x₀) (hV: Stores.till x₀ ≤ c.val)
    (he:Meadow.Budget (V) (Beam.marquee Z' V).reg (High.leftover (Σp) O k γ|>.logRead) (z ^ seam_hat I)) (x:Positions (Uniform.Primary c G)) (hp:flags (Pressure.temp x₀) (actual x)=∅) (hq : ‖x‖+2*furl G L x₀ < eaves G L x₀):
    ∀ l:List (Directions G c), l.length≤(V).order→ (∀ v∈l,‖v‖≤(V).threshold) → ‖leftDerivs (stillA (Trio.froth (ledgerV A F π Z' k))) l (actual x)‖ ≤ ticket (V).order g₀+2*((Fintype.card (Site c):ℝ)*(z^ seam_hat I)) := by
  obtain ⟨_,_,_,hX⟩:= F.inn.chip J x₀ (A.B.valid.pays m) I (step_paid A.B.a m)
  let X' := Token.arrayE Σ₀ V₁ β γ; let f:=ledgerV A F π Z' k; let h:=Trio.froth f
  obtain ⟨hv,hi⟩:= weight A F π hm Z' hz K; have hh : (V).threshold ≤ 2*Pressure.fiery G x₀ L:=by rw [← Z'.laws.data.funds.length_eq]; exact Z'.laws.data.room.temperatures
  have hH : (V).Regular univ h:= by rw [show h=∑ i,f i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> CouplingShape.reg_extend (palaces A F H π Z' hz hm k i) (subset_univ _)
  have heq:(V).order= (E).order:= congr_arg RG.Stage.order (params_eq A.B.valid m)
  have hT x' (hi':x'∈sunny V): X' x'=weighty Z' O K*↑(Fintype.card (Site c))-h x'-Boulevard.throng (High.leftover (Σp) O k γ|>.logRead) x':= by
    apply High.chants _ _ _ hv _ hU _ (A.B.support.cap N _ hm.le) (smoky hi')
    have hβ: U.beta=β:= hU ▸ rfl; nth_rewrite 1 2 [← hβ]; exact hi _
  intro l hl hb; rw [heq]; apply hX _ rfl hh heq c x hq hp _ _ h X' g₀ (z^ seam_hat I) _ he hH hT ?_ l hl hb
  intro y hy htX; let θ:=Greenbelt.prism Σ₀ x₀ O (F.shape.o J I).K (actual y) K
  have ht : flags (Pressure.temp x₀) (actual y)=∅:= smoky («P»:=V) htX
  have hp : Cash (F.walls J I) x₀ (F.shape.μ J I) L (F.target J I) (F.shape.o J I) (F.shape.c J I) Σ₀ (virgin Σ₀ V₁ β):= hU ▸ Z'
  have hk := Pane.burst D F.shape A (permits0 A F sH) F.floor hm π K (F.settles _ _) hV (issued A F π Z' hm hU hf) hp θ rfl rfl ht.symm ht y rfl hy
  have hh : (stillA X') ∘ actual= Shellac.off (Token.harmony Σ₀ V₁ β γ):= funext fun i=> by simp only [Function.comp_apply,Shellac.off, Pi.sub_apply,stillA,X',Token.harmony, map_zero,link_one]
  rw [hh]; exact hk.2
end YM.AllOrder.Shop
