import YM.LocalLTE.Furnace.Loom
/-! Actual Physical earned. PRE price mask. Same K Forecast. -/
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
open YM.LocalLTE.Inset ClockB
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {c f:Side} {κ q η l e w : ℝ} {p' : ℕ} (W:Wind p' η) {m n j k N :ℕ} (hm:m<N)
    (hk:Reliable G κ q) {d:ℕ→ℕ→ℝ}
    (hV:Roof.WorksIn R A.post A.delay S) (hX:Spoke D R W A.post κ d A.delay)
    (h:Rich R (1/16) A.delay)
    (hP: Tenement R A.delay)
    (hp: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
    (hS: (X.p.profile (A.B.a.clock.J m)).supportExponent+3≤ (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn)
    (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "b" => Trio.resize W.ℓ (Rain.lint C A m)
local notation "z" => Trio.base b (radiusB x₀)
local notation "D₀" => Meadow.studioN W.ℓ (Rain.lint C A m) (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "L" => D.L Jp
local notation "g" => gold G L x₀
local notation "γ" => A.B.kin.alpha N m
local notation "t" => X.p.profile Ip
local notation "s₀" => ClockB.lanternPay G L t W.q x₀
local notation "V" => vista D (C:=C) W.ℓ
local notation "χ" => Chi.canonical
local notation "C₀" => yside (C:=C) (m:=m) (A:=A) W
local notation "P₀" => scene (C:=C) (m:=m) (A:=A) W
local notation "T" => Pane.orchestra A N
variable {V':RG.Rep G (A.B.a.S.side (m+1) n)} (hR:Receiving R S A.delay (1/8))
    (U : Guide A.B R N m n V') (hU : Opera.Price A.B R N m n V' U)
    (hl:Lives A.B.bake N (m+1) n V') (hb: V'.beta ∈ band A.B.a (m+1))
    (X': Expose (A:=A) (R:=R) W V'.beta N m)
    (k:ℕ)
local notation "fa" => X'.read W k
local notation "Q" => fronts (m:=m) (A:=A) (C:=C) W
set_option quotPrecheck false
local notation "LL"=> lossFee G L (Z Jp Ip).wanting b (X.p.profile Ip) x₀
local notation "S₀" => A.B.a.S.oneStep m n
local notation "Y₀" => (YM.LocalLTE.Patch.failure B Q z fa U γ W.ℓ k)
include X' hU hR hl hb hS hP hp hV hX hm hr
-- copying Marlin path, paying gluing at studio N. Does not preserve
-- K addresses for comparisons yet.
lemma hauls (i:Site A₀): Tidy B (neighbors (2*z) i) (Y₀ i)∧ (∀ P,Y₀ i P≠0→¬Healthy (B).threshold (neighbors (2*z) i) P) ∧ (∀ P, ‖Y₀ i P‖ ≤ lossFee G L (Z Jp Ip).wanting b t x₀):= by
  let α:=(B); let V₀:= Meadow.intern U; let hc:= T (S₀).exact_size
  have hx : D₀ ≤ Meadow.studio b (radiusB x₀):= studioCmp _ _ α.B_pos
  let F'' i:=Classical.choice (Tree.select (panel A m (P₀ i)).ratio (panel A m (P₀ i)).patch.odd_side)
  have hz:=Urns.volume (m:=m) (n:=n) W hX ; have he':=Boulevard.lays R A (S₀).exact_size V₀ hV.chip hm hP hr hS hp hU (Classical.choice (Tree.select (A.B.a.clock.op m n).ratio (A.B.a.clock.op m n).patch.odd_side)) |>.1
  have hF (i:Stars):= Boulevard.lays R A (P₀ i) (Meadow.intern (X'.posts i)) hV.chip hm hP hr hS hp (X'.lands i) (F'' i)|>.1
  let a:= X'.read W k; have hY i j:α.Regular univ (a i j):= X'.gain W hm hV hP hp hS hr k i j
  have hW : tent b (radiusB x₀)+4 ≤ z:= by unfold Trio.base; omega
  have hm : 2*D₀ ≤tent b (radiusB x₀):= by unfold Trio.tent; omega
  refine ⟨Trio.primN B V₀ γ k Q z a i he'.smooth hY hW (by change D₀ ≤ _; omega) le_rfl rfl, fun P hYp hΩ=> hYp (Trio.scrapN B V₀ γ k Q z a i le_rfl hW hm hz.2 rfl rfl rfl rfl (Trio.cagedN R A (S₀).exact_size (fun i=>scene (C:=C) (m:=m) (A:=A) W i) V₀ X'.posts hb (hl.path.trans (congr_fun (congr_fun A.B.bases N) _)) hl.point hV.chip hR.grow.1 (by assumption) hP hr hS hp hz.2 (fun i=>le_trans (by gcongr) (Trio.highChair b _ i|>.1)) he' rfl rfl rfl) hΩ),fun P=>?_⟩
  let f:= heat G L (Z Jp Ip).wanting b t x₀; let g':= (ballCost D₀:ℝ)
  obtain ⟨hi,hJ,hΨ,hΓ⟩:=Rain.jersey (m:=m) (A:=A)
  have h' : g'*(turnFee B * (betaF G x₀ L ^ (Z Jp Ip).wanting + betaF G x₀ L ^ (-(7/16):ℝ))) ≤ f := by
    have hh := he'.H_nonneg; unfold f Trio.heat; rw [← hΓ]; unfold g' ballCost; gcongr
  have hh i (P:Config G (C₀ i)) (hx:flags (B).threshold P=∅) (u:Site (C₀ i)) : ‖a i u P‖ ≤ f:= (Trio.skinN (J₀:=W.ℓ) B P (Meadow.intern (X'.posts i)) γ k u (hF _) rfl rfl rfl rfl hx).trans h'
  exact (Trio.augustN (J₀:=W.ℓ) B P V₀ γ k Q z a i he' rfl rfl rfl rfl (fun _=>f) hh hW).trans (add_le_add (add_le_add h' h') le_rfl)
-- Forecast genuine authority. INPUT INVOICES.
set_option maxHeartbeats 400000 in
lemma stakes : Ingredients (YM.LocalLTE.Patch.marked B U z) (Marlin.dummy (YM.LocalLTE.Patch.deposit B Q z fa U γ W.ℓ k)) (raiser B) 0 (Time.forecastK A.B.a m S V'.beta):=by
  let pk:=forecastK A.B.a m S V'.beta; let H:= YM.LocalLTE.Patch.inventory U γ W.ℓ k; let Wt:= Meadow.intern U; let F₀:= Beam.marquee U B
  have he i:= hauls W hm hV hX hP hp hS hr hR U hU hl hb X' k i
  have ht s y: Nonempty ((F₀.read H).Moves s y):= Beam.moves _ _ Chi.canonical _ s y _
  let c:=Marlin.tithe (2*z) LL (B) (coverTicket b)
  have hs' i : (coverNumber (B).B (neighbors (2*z) (i:Site (A₀))):ℝ) ≤ coverTicket b:= by
    unfold coverTicket; apply Nat.cast_le.mpr; apply le_trans (Trio.scaleMeters b (radiusB x₀) (B).B_pos i _ le_rfl); rw [two_mul]
  have ht' : 0 ≤ lossFee G L (Z Jp Ip).wanting b t x₀ := (norm_nonneg _).trans ((he 0).2.2 1)
  have hf:0≤ c:=by unfold c Marlin.tithe; positivity
  let y:=Cash.armK (C Jp Ip) L (R.μ Jp Ip) x₀ 0 (Z Jp Ip).degrees
  have hh : y ≤ pk/8:= (Opera.backing A.B R hR hb).trans_eq (by unfold pk; ring)
  obtain ⟨hi,hJ,hΨ,hΓ⟩:=Rain.jersey (m:=m) (A:=A)
  have hK : (raiser B).supportExponent+1≤ (Z Jp Ip).earn:= by change (B).supportExponent+1+1 ≤_; rw [hΨ]; linarith only [hS]
  obtain ⟨v',hj,hj'⟩:= Refrain.chargesOut (raiser B) U Wt χ hU rfl hK
  let lam':=step_paid A.B.a m; have hΛ:= hX.cash _ _ lam'|>.2 _ (A.B.valid.pays m)
  obtain ⟨-,-,hT,_⟩:= hV.terms.allot Jp Ip lam' _ (A.B.valid.pays m)
  let a β:=(S Jp Ip).pair.strong (betaF G x₀ L) β
  have hν : Next.Scheduling.inBand (betaF G x₀ L) V'.beta:=by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hb
  have hv : pk = a V'.beta := by unfold pk forecastK; rw [PriceCompiler.beta_eq A.B.valid]
  have he':c ≤ betaF G x₀ L ^ (-(1/8:ℝ)):= by unfold c Marlin.tithe; rw [hΨ]; exact hΛ.tithe
  change Ingredients _ _ _ _ pk; rw [hv]; obtain ⟨η,hg⟩:= hT _ hν y c (budget_nonneg (hj' 0)) hf (show y≤ a _/8 from hh.trans_eq (congr_arg (fun i:ℝ=>i/8) hv)) he'
  exact Marlin.stakes (B) F₀ z (2*z) H _ _ (Refrain.qualified _ _ _ _ _ _ rfl) ht hg hj hj' (fun i=> (he i).1) (fun i=> (he i).2.1) (fun i=> (he i).2.2) hs' (le_refl c)
end YM.PhysicalNext.Repeat.Urns
