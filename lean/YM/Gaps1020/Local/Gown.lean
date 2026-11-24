import YM.Gaps1020.Local.Dress
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
local notation "Θ"=> X.p.profile j0
local notation "ℓ₀" => turnFee P₀
local notation "Δ" => ℓ₀ * ((Z^(M+1))⁻¹)
local notation "z"=> noteX W H.knows x.val
local notation "d'"=> H.ordinal
local notation "V'" i=> Rain.moor R.target A m i
local notation "Y!" i=> H.W.tiers i z
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
-- Πρδ. Paints this term alone on post X! **with true K**. It's allowed to
-- include internal media-dependent lookups (K unanalyzed apart payment).
-- No assert redoing grantors δ/K with epoch approximation.
def sweep (H:Spring R N m n l s Y) (f:Magazine H.H.base→ Config G (A.B.a.S.side m n)→ℝ) (i:Magazine H.H.base): Config G (A.B.a.S.side m n)→ℝ:= if i∈ Meadow.bouquet H.H.base H.ordinal then 0 else f i
def realize (f:F')(g:Trio.Offer G C0): Collection.Source G C0:=
    ⟨(Marlin.bison ({logRead:=choir (sweep H f) ∘ pennant E0,hardRead:=hg1}:Collection.Source G C0) g (Rain.lights W H.knows H.W d' x.val)).regular,(X!).hardRead⟩

def earnest (M:ℕ):= realize H x (Post.jointE X0 (Tᴹ M) M O) (defect H x M)
def paintLow (M:ℕ):= realize H x (Post.retainedE X0 M O φ) (cue H x M)
-- path EXACT. Across any points in T over actual parameter family beyond E0 base if differs. No statements of regularity in x.
variable (M)
lemma statement : (X!).logRead=(paintLow H x M).logRead + (earnest H x M).logRead:=by
   -- at Beam roster H.H.base fill; verify log even off masks
   have ht := Post.piecesAll (M:=M) X0 O φ
   let f := cue H x M; let u:= defect H x M
   have hd : X! = paint W H.knows H.W d' x.val:= rfl
   funext i y; unfold Rain.paint graft poursP; dsimp only [Marlin.bison,Function.comp_apply,realize,paintLow,earnest,uptick]; rw [(W).click x x.property]; simp only [Pi.add_apply,Function.comp_apply]; rcases h:(leanU C0 i) with j|j; simp only [Sum.elim_inl];
   · let k:= ((pennant E0) j); let u':= k.1.view y
     have hx:Mallow.houseS H (⟨x.val,x.property⟩:Set.Icc l s)= S0:= rfl; have hi: (W).sister (⟨x.val,x.property⟩:Set.Icc l s)=X0:=rfl
     let t:= if k.2∈ Meadow.bouquet E0 d' then 0 else opus E0 X0 O φ k.2
     change Rim C0*t u'= Rim C0*sweep H _ _ u'+Rim C0*sweep H _ _ u'; unfold sweep t
     split; · simp
     rw [(ht k.2),Pi.add_apply,mul_add]
   simp only [Sum.elim_inr]; change Rim C0*(beacons W _ _ _ x.val j.2 (j.1.view y))=Rim C0*f j.2 (j.1.view y)+Rim C0*u j.2 (j.1.view y); rw [beacon (M:=M)]; exact mul_add ..

-- Give price and real Moves. No norm loss from K duplicate. `Collection.Local` 
-- retains extra + costs. pasting move's ep independent of gas tickets.
include h
lemma lawfulMotion (f:F') (g:Trio.Offer G C0) (i:Signed) (s:Site C0): Nonempty (((pX).read (realize H x f g)).Moves i s):=by
   have ht:= Beam.moves E0 P₀ O X0 i s (sweep H f)
   -- applies at lens/bison before pluck, but K equality not needed
   obtain ⟨P⟩:=ht
   obtain ⟨q⟩:= Marlin.reeds P' e (2*e) ({logRead:=choir (sweep H f) ∘ pennant E0,hardRead:=hg1}:Collection.Source G C0) g (Rain.lights W H.knows H.W d' x.val) i s P
   obtain ⟨a⟩:= (H.core h _ x.property).transforms i s
   exact ⟨q.ep,a.kp,q.reg_site,q.reg_support,a.forced_support,a.forced_inventory,a.forced_tests,q.valuesE,a.valuesK⟩

local notation "Φ" => seatNeed A wid m Δ
local notation "T" => Real.exp (preExponent P₀*coverTicket wid)
abbrev demand (A:Alloy X D)(k m:ℕ)(w:ℝ):ℝ:= w + turnFee (A.B.a.budget m) * (seatNeed A k m w*Real.exp (preExponent (A.B.a.budget m) * coverTicket k))
local notation "DEMAND" => demand A wid m Δ
include he hM
set_option maxHeartbeats 470000 in
lemma prePartials : Collection.Local pX P₀ (earnest H x M) DEMAND k0 ∧ Collection.Local pX P₀ (paintLow H x M) (forecastE A.B.a m + DEMAND) k0:=by
   let B:= P₀; let F :=Post.jointE X0 (Tᴹ M) M O; let t : Collection.Source G C0:= ⟨choir (sweep H F) ∘ pennant E0,hg1⟩
   let C':= A.B.a.S.oneStep m n |>.exact_size; let y:=Beam.marquee E0 P₀
   have hh: Meadow.Budget (P₀) (Beam.marquee E0 P₀).reg t.logRead Δ:= by
      let U: Guide A.B R.shape N m n (Y x.val):= houseS H x
      have hE:= generalPane (N:=N) h he hM (A.B.a.S.oneStep m n|>.exact_size) _ _ E0 U X0 (fun k=> k∉ Meadow.bouquet E0 d') -- defeq panel?
      let f:Magazine E0→ Config G C0→ℝ:= fun i=> if i∉Meadow.bouquet E0 d' then F i else 0
      have hF: f = sweep H F:= by funext i; unfold sweep f; split_ifs<;> rfl
      change Meadow.Budget B y.reg (choir (sweep H F) ∘ pennant E0) Δ; convert! hE using 1; funext i U; unfold sweep choir; dsimp only [Function.comp_apply]; split_ifs<;> first| rfl | contradiction
   have hp:0≤Φ:= (purchaseD H x h he hM (0:Site C0)).2.1; let f:= defect H x M
   have hP : Meadow.Budget B (leap e) f (Φ*T):=by
      refine ⟨fun _=>Φ,fun i=> ?_,fun i=> purchaseD H x h he hM i⟩; apply budget_finite
      · intro i; split; exact mul_nonneg hp (Real.exp_pos _).le; rfl
      rw [Finset.sum_eq_single i]; rw [if_pos (show (Marlin.leap e i).site=i from rfl)]
      · apply mul_le_mul_of_nonneg_left _ hp; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters wid (radiusB x₀) (P₀).B_pos i e (by omega)).trans; rw [two_mul]
      · intro j hj h'; exact if_neg h'
      · simp
   let k' := forecastK A.B.a m R.scout (Y x.val).beta
   have h0:= H.core h _ x.property; have ht:= Marlin.reg_bison y e (2*e) t f (Rain.lights W H.knows H.W d' x.val) hh hP -- replace
   have h' : Collection.Local pX P₀ (earnest H x M) DEMAND k':=by
      obtain ⟨f,hf,hq⟩:= ht
      exact ⟨fun i=> (hq i).1,⟨h0.family.sym,h0.family.symtest,h0.family.meas,h0.family.meas_test,h0.family.reads,h0.family.reads_test,h0.family.permit⟩,lawfulMotion H x h F (defect H x M),⟨f,fun i=> (hq i).2,hf⟩,h0.expensive⟩
   exact ⟨h',Vacuum.subLocal h0 h' (eq_sub_of_add_eq (statement M H x).symm) rfl (lawfulMotion H x h _ _)⟩
end YM.GapsLocal.Renew
