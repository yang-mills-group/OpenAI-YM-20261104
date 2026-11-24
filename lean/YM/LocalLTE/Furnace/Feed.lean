import YM.LocalLTE.Furnace.Now
/-! Actual Machine consumer. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Urns
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- compact socket avoids Pie SAM goals; not obligation records encoding analytic estimates.
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {E:ℕ→ℕ→Exchange} {bt:Baton G} {u t : Return.Wages} {Bn:ℕ→ℕ→Booth} {J:ℕ→ℕ→JointLoad.Clockwork.Menu} {P:ℕ→ℕ→JointLoad.Heir.Record} {L : ℕ→ℕ→JointLoad.Folio.Aux} {c c₁ c₂:ℝ} {q:UVNext.CouplingReset.ResetPrices} {η:ℕ→ℝ} {r:ℕ→ℕ→ℕ} {T:Programs X.p} {Y: ℕ→ℕ→Cafe}
    (h : Roof.Sheltered (C:=T) (B:=Y) A bt u t r Bn J P L R S (1/16) (1/16) (1/8) E q η)
    {N m n : ℕ} {Q: UVNext.CouplingReset.In A.B.a m n} {a:ℝ} (hm: m<N)
open YM.LocalLTE.Inset ClockB
variable {l κ q' η' : ℝ}{p' ℓ:ℕ}(W:Wind p' η') (hk : Reliable G κ q') {d:ℕ→ℕ→ℝ}
    (hV:Roof.WorksIn R A.post A.delay S) (hX:Spoke D R W A.post κ d A.delay)
    (ht:AsDivisors A.B.a.S)
    (hC: (C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O)
    (M:Maps (A:=A) (C:=C) W m N)
    {V':RG.Rep G (A.B.a.S.side (m+1) n)} (hl:Lives A.B.bake N (m+1) n V') (hb:V'.beta∈band A.B.a (m+1))
    (U:Guide A.B R N m n V') (hU:Opera.Price A.B R N m n V' U)
    (X':Expose (A:=A) (R:=R) W V'.beta N m)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "b" => Trio.resize W.ℓ (Rain.lint C A m)
local notation "z" => Trio.base b (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "T'" => A.B.a.clock.op m n
local notation "e₁" => Time.forecastE A.B.a m
local notation "k₀" => Time.forecastK A.B.a m S V'.beta
local notation "s₀" => ClockB.lanternPay G (D.L Jp) (X.p.profile Ip) W.q x₀
local notation "γ" => A.B.kin.alpha N m
local notation "T₁" => (A.B.a.params m)
local notation "T₀" => (X.p.profile Ip)
local notation "Ce" => (((1/16+2*(1/16:ℝ)))*Time.forecastE A.B.a m)
local notation "ζ"=>betaF G x₀ (D.L Jp)
local notation "Q'"=>fronts (m:=m) (C:=C) (A:=A) W
local notation "PU"=>Meadow.intern U
local notation "χ"=>Chi.canonical
local notation "f'"=> M.reader W κ (d Jp Ip) (gStep V'.beta)
set_option quotPrecheck false
lemma aware {i:Side} {X:Listing G i}{a b' : ℝ}{U:Collection.Source G i} (P':BudgetPoint) (h:Collection.Local X P' U a b') : Compared X P' (fun _=> U) (Set.univ: Set ℝ):=by
  have hh : (X.read U).KBound P' b':=by
    obtain ⟨f,h,hq⟩:=h.expensive; refine ⟨f,h,fun i=> budget_mono (hq i) (fun j=> ?_) ?_⟩
    · split; unfold BudgetPoint.mass; exact mul_nonneg (Real.exp_nonneg _) (h _|>.1); exact le_rfl
    intro j; split; next hp=> dsimp only [Listing.read] at hp ⊢; rw [if_pos hp]; unfold BudgetPoint.mass; rw [mul_comm]; gcongr; exact h _|>.1; linarith
    exact (hq i).1 _
  obtain ⟨u,hh,hp⟩:= Activities.K_total hh; obtain ⟨w,hw,hq⟩:=Activities.E_total h.unweighted
  exact ⟨fun i he=> ⟨fun i x hx=> Eventually.of_forall (fun _=> ⟨hx.le,fun _ _ _ _ _=> by simp [hx.le]⟩), fun i x hx=> Eventually.of_forall (fun _ _=> by simp [hx.le])⟩,fun i h t hx=> ⟨id,w,u,tendsto_id, hw,hh,⟨hq,hp⟩,Eventually.of_forall fun _=>⟨hq,hp⟩⟩⟩
lemma uniform_curve {i:Side}(P:BudgetPoint)(X: RG.Rep G i):Curve P (fun _=> X) (Set.univ: Set ℝ):=by
  refine ⟨continuousOn_const,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,fun q h x hx=> Eventually.of_forall (fun _=> ⟨(fun _=>0),(fun _=>0),fun _=>⟨le_rfl,fun _ _ _ _ _=> by simp⟩,fun _ =>by simp,?_,?_⟩)⟩
  all_goals simp [BudgetPoint.mass,SumBudget,h.le]
-- Real data
variable (hs:G.Simple)
include hV hX hk M hU ht hC h hb hl hm hs
local notation "fB" => (A.B.a.budget (m+1))
abbrev baked (k:ℕ) := Return.result A.B N (fun _=> V') (stock W U) (fun _=> reads W U X' k) (0:ℝ)
structure Firings (S:Time.Scouts (F:=F)) (κ d' : ℝ) (k:ℕ) (Y:ℕ→ℕ→Cafe) (G₀:Forest (A.B.a.clock.op m n).ratio) (k':Return.Bookings A.B m n p) : Prop where -- T'' remove, ζ in Maps
  flowing : Return.atlas A.B N G₀ k' Chi.canonical (radiusW Y) V' (stock W U) (reads W U X' k) (tattoo W U G₀ k)
  wallet : Collection.Local (stock W U) (A.B.a.budget m) (reads W U X' k) (Time.forecastE A.B.a m) (Time.forecastK A.B.a m S V'.beta)
  ancestry : Meadow.Budget (A.B.a.budget m) (stock W U|>.reg) (earnt U) Ce
  pressure : Meadow.Budget (A.B.a.budget m) (stock W U|>.reg) (smog W M U X' d' κ k) (quota W A m)
  licenses : Return.licensed A.B N G₀ k' Chi.canonical (radiusW Y) V'
  offer : A.B.Move N m n (baked W U X' k) V'
  fare : (baked W U X' k|>.v) = Collection.vac (reads W U X' k) (tattoo W U G₀ k)
set_option maxHeartbeats 300000 in
lemma feeds (A':Forest (A.B.a.clock.op m n).ratio) (k':Return.Bookings A.B m n p): ∀ᶠ k:ℕ in atTop,Firings W M U X' S κ (d Jp Ip) k Y A' k':= by
  let c:= h.conducts; let T:= c.machine
  have hp:= Urns.decency h hm hl hb; have hi := h.agenda _ _ (step_paid A.B.a m)|>.1
  filter_upwards [Urns.lights W hm hV hX h.peak h.jewels hp hi c.full (A.B.a.S.oneStep m n).exact_size U hU, X'.duration W hm hV hX h.peak h.jewels hp hi c.full] with k hf hG
  have hu:= Urns.charged h hm W hV hX ht hC M hl hb U hU X' k hf hG -- binder
  have hh:= Urns.authority h hm W hk hV hX ht hC M hl hb U X' k hf hG
  have hz:Return.atlas A.B N A' k' Chi.canonical (radiusW Y) V' (stock W U) (reads W U X' k) (tattoo W U A' k):= (Return.earnings A.B N A' k' Chi.canonical (radiusW Y) T.ring T.bill hm V' hl hb).2.2.symm.trans (funext fun i=> Urns.flowing h hm W hV hX hl hb U hU X' k hf A' i)
  obtain ⟨he,hK,_h,_hh,hΓ⟩:= T.run (l:=Set.univ) («Q»:=fun _=>V') (τ:=fun _=> tattoo W U A' k) hm (fun _ _=>⟨hl,hb⟩) hs A' k' Chi.canonical (fun _ _=>hz) (fun _ _=>hu) (aware (B) hu) (uniform_curve fB V')|>.2 (0:ℝ) (Set.mem_univ _)
  exact ⟨hz,hu,Urns.tollgate h hm W hl hb U hU,hh,he,hK,hΓ⟩
end YM.PhysicalNext.Repeat.Urns
