import YM.LocalLTE.Furnace.Maps
/-! Material mask quilting. eta after tomorrows. -/
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
variable {β:ℝ} (X': Expose (A:=A) (R:=R) W β N m) (M:Maps (A:=A) (C:=C) W m N) (ht:AsDivisors A.B.a.S)
   (hC:(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O)
   (hq: X'.Yields W k)
local notation "P'" => fronts (m:=m) (A:=A) (C:=C) W
local notation "f₀"=> X'.read W k
local notation "f'"=> M.reader W κ (d Jp Ip) (gStep β)
-- World Price
lemma tickets_leap {b' : ℝ} (U: Trio.Offer G (A.B.a.S.side m n)) (hp:∀ i:Site A₀,(B).Regular (neighbors z i) (U i)∧(B).supBounds i (neighbors z i) (U i) b'):
    Meadow.Budget B (leap z) U (b'*Real.exp (stout (X.p.profile Ip)*coverTicket b)):= by
  have h': 0≤b':= (hp 0).2.1
  refine ⟨fun _=>b',fun i=>budget_finite (fun i=>?_) ?_,hp⟩
  · split; exact mul_nonneg h' (Real.exp_nonneg _); exact le_rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (leap z i).site=i from rfl)]
  · have hz : preExponent B=stout (X.p.profile Ip):= by unfold preExponent stout; rw [(Rain.jersey (A:=A) (m:=m)).2.2.1]
    rw [← hz]; apply mul_le_mul_of_nonneg_left _ h'; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters b (radiusB x₀) (B).B_pos i z (by omega)).trans; rw [two_mul]
  · intro j _ h; exact if_neg h
  simp
include hX hm hV ht hC hP hp hS hr hq M
-- price actual first
lemma textile :
    Meadow.Budget B (leap z) (Expose.rays W X' k (A₀)) (planks G L b t x₀*Real.exp (stout (X.p.profile Ip)*coverTicket b)):= by
  let fa:= f₀
  have hK:= hX.cash _ _ (step_paid A.B.a m)|>.2 _ (A.B.valid.pays m); obtain ⟨hi,hJ,hΨ,hΓ⟩:=Rain.jersey (m:=m) (A:=A)
  have hv := hK.light.1; let Q:= B; let f:= Trio.crestFeat G L b t x₀
  have h (i:Stars) : 0 ≤ f i:= by unfold f; dsimp only [Trio.crestFeat]; rw [← hΓ]; have he : 0 ≤ gold G L x₀:=Real.rpow_nonneg (zero_le_one.trans hv) _; unfold Boulevard.ticket; have hN:= turnFee_pos Q; change _ ≤ _+2*(_*(turnFee Q*(gold G L x₀+gold G L x₀)+gold G L x₀)); positivity
  have hh : ∀ i j,Q.Regular univ (fa i j):= X'.gain W hm hV hP hp hS hr k
  have hz i : Q.Regular univ (Trio.froth (fa i)):= by rw [show Trio.froth (fa i)=∑ j,fa i j from funext fun V'=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j hd=>hh i j
  have hW : tent b (radiusB x₀)+4 ≤ z:= by unfold Trio.base; omega
  refine Urns.tickets_leap W _ fun i=> ⟨?_,?_⟩
  · unfold Expose.rays; rw [Trio.orchard]; exact YM.LocalLTE.Patch.regular B P' _ hW i hz
  rw [← (Trio.loses G L b t x₀ (B) hi hJ).2]; apply Trio.kinds B P' z fa hh h hW (Sienna.furl G L x₀) (eaves G L x₀) i ?_ (fun l x hx h => Urns.golds W hm hV hX hP hp hS hr ht hC l (M.tree l) _ (X'.lands l) (hq l) x hx h)
  intro U hU j; have he : Q.threshold≤ 2*Pressure.fiery G x₀ L:= by
    rw [← (X'.posts j).laws.data.funds.length_eq]; exact (X'.posts j).laws.data.room.temperatures
  obtain ⟨u,x,hx,hΩ⟩:= hK.frame Q he _ ((Urns.volume W hX).1) i U hU j
  exact ⟨u,x,hx,hΩ.trans_le (Real.rpow_le_rpow_of_exponent_le hv ((W.oak'.trans W.cedar).le))⟩

include hk
lemma tessera : Meadow.Budget (B) (leap (c:=A₀) z) (YM.LocalLTE.Patch.light f₀ P' f')
    (ClockB.gust G L t b W.l W.q x₀*Real.exp (stout t*coverTicket b)):= by
  let fa := f₀; let s':= f'; let Q:= B; have hh:= hX.cash _ _ (step_paid A.B.a m)|>.2 _ (A.B.valid.pays m); have hv':= hh.light.1
  obtain ⟨hi,hJ,hΨ,hΓ⟩:=Rain.jersey (m:=m) (A:=A)
  let p i:=Urns.rose W hm hk hV hX hP hp hS hr ht hC i (M.tree i) _ (X'.lands i) (hq i) (M.station i) (M.shares i) (M.notes i)
  let f:=ClockB.ease G L t b W.l W.q x₀; have hp i: Q.Regular univ (Trio.froth (fa i)+s' i):=(p i).1
  have hx : 0 ≤ (s₀):= by
    unfold ClockB.lanternPay ClockB.lanternPay.turnCost_dummy; rw [←hΓ]; have hz:=turnFee_pos Q; have he:=Real.rpow_nonneg (zero_le_one.trans hv') W.q; change 0≤turnFee Q*(betaF G x₀ L^W.q+betaF G x₀ L^W.q)+(betaF G x₀ L)^W.q; positivity
  have hv (i:Stars):0≤ f i:=by unfold f; dsimp only [ClockB.ease]; unfold Boulevard.ticket; have he:= Real.rpow_nonneg (zero_le_one.trans hv') W.l; positivity
  have he : ClockB.gust G L t b W.l W.q x₀ = Trio.oroW B z f:= by unfold ClockB.gust Trio.oroW Trio.tilt; rw [hi,hJ]
  have hW : tent b (radiusB x₀)+4 ≤ z:=by unfold Trio.base; omega
  rw [he]; apply Urns.tickets_leap; intro x; refine ⟨YM.LocalLTE.Patch.localLight B fa P' s' hW x ?_ ?_,YM.LocalLTE.Patch.pay_patch B fa P' s' hW x (a:=cone W.u (betaF G x₀ L)) (e:=Sienna.furl G L x₀) hv hp ?_ (fun i=> (p i).2)⟩
  · intro i; exact YM.LocalLTE.Frame.authorized (B) _ hk (show ContDiff ℝ _ _ from smoothSong (M.tree i) (T (P₀ i)) (C Jp Ip).table _ _ _ (M.notes i) p' _ _)
  · -- Regular all grid
    intro i; rw [show Trio.froth (fa i)=∑ j,fa i j from funext fun V'=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j hd=> X'.gain W hm hV hP (by assumption) hS hr k i j
  intro U hu i; apply hh.frame Q _ _ ((Urns.volume W hX).1) x U hu i; rw [← (X'.posts i).laws.data.funds.length_eq]; exact (X'.posts i).laws.data.room.temperatures
end YM.PhysicalNext.Repeat.Urns
