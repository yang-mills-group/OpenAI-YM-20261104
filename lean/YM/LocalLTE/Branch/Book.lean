import YM.LocalLTE.Branch.Pin
/-! Post Move Bulletin. Exact δ,v, model independent of old dictionary. -/
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
-- addresses from PET template. high kinetic independently determined too. Z depends M.Path, order, threshold, level m,N,n.
open Magnet
local notation "K₀" => A.B.kin.path N m
local notation "a₀" => (A.B.a.params m)

def outer (n:ℕ): Listing G (A.B.a.S.side m n) := -- beware A0 notation n
  let y:=A.B.a.S.side m n
  let u:ℕ→ RegularAddress y:= fun _=> (drawer G y).reg 0
  let f:ℕ→ForcedAddress G y:= fun _=> (drawer G y).kernel 0
  Marlin.pluck B (Marlin.lodge ⟨u,f⟩ z (2*z))

abbrev printed (κ d ν : ℝ)(n:ℕ):= advanced (outer (m:=m) (A:=A) (C:=C) W n) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (corePlan W M κ d ν n) γ
abbrev royalty (κ d ν:ℝ)(n:ℕ):= VerifiedReset.Averaging.delta ((outer (m:=m) (A:=A) (C:=C) W n).read (Magnet.seed (corePlan W M κ d ν n)))

def postAncestor := advanced (stock W U) K₀ (T₁).clip B (earnt U) 0
def postFog (κ d:ℝ) (k:ℕ):= advanced (stock W U) K₀ (T₁).clip B (smog W M U X' d κ k) 0
abbrev heirΔ := VerifiedReset.Averaging.delta ((stock W U).read (seed (earnt U)))
abbrev mistΔ (κ d:ℝ) (k:ℕ):= VerifiedReset.Averaging.delta ((stock W U).read (seed (smog W M U X' d κ k)))

local notation "q₀"=> quota W A m
local notation "δT"=> VerifiedReset.Averaging.delta
variable (hG:G.Simple) {k:ℕ}{G₀:Forest (A.B.a.clock.op m n).ratio}{k':Return.Bookings A.B m n p} (hx:Firings W M U X' S κ (d (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) k Y G₀ k')
local notation "R'" => (stock W U)
local notation "s'" => (reads W U X' k)
local notation "d₀" => d Jp Ip
local notation "f₀" => corePlan W M κ (d Jp Ip) (gStep V'.beta) n
local notation "H"=> earnt U
local notation "e₀" => smog W M U X' (d Jp Ip) κ k
local notation "P'" => (A.B.a.S.side m n)
local notation "D'" => (baked W U X' k)
local notation "F'" => (printed W M κ d₀ (gStep V'.beta) n)
-- δ(price-independent). Pay transformed
lemma realm : advanced R' K₀ (T₁).clip B f₀ γ= F' ∧ δT ((R').read (seed f₀)) = royalty W M κ d₀ (gStep V'.beta) n:= by
  let Q:= fun i=> ∃ v:Door (P'), Marlin.leanU (P') i= .inr v; let R₀:= outer (C:=C) (m:=m) (A:=A) W n; let S:= (f₀)
  have hz:∀ i, Q i→ (R').reg i= R₀.reg i:=by
    rintro i ⟨j,hj⟩; let v:= (Beam.marquee U B); change Sum.elim v.reg (Marlin.sea z) (leanU (P') i) = Sum.elim _ (Marlin.sea z) (leanU (P') i); rw [hj]; rfl
  have he:∀ i,¬Q i→ S i=0:=by
    intro i hi; unfold S corePlan YM.LocalLTE.Patch.planned; cases hv:Marlin.leanU (P') i
    · rfl
    next k=> exact False.elim (hi ⟨k,hv⟩)
  exact ⟨Magnet.pinnable B hz he _ _ _, Magnet.moderate B hz he⟩
lemma roll  : (D').beta=V'.beta+γ+δT ((stock W U).read s') ∧ (D').activities.reg=(drawer G P').reg ∧
    (D').activities.E=advanced (stock W U) K₀ (T₁).clip B (s').logRead γ:= by
  -- NOTE grouping predictor = beta+ α sign. Result uses template.trial.
  exact ⟨rfl,rfl,rfl⟩

lemma minus_cost {i:Side}{QT:ℕ→RegularAddress i}{P:BudgetPoint}{V Lh:ℕ→ Config G i→ℝ}{u v:ℝ}(h:Meadow.Budget P QT V u)(hh:Meadow.Budget P QT Lh v): Meadow.Budget P QT (V-Lh) (u+v):= by
  obtain ⟨f,h,hp⟩:=h; obtain ⟨d,hD,hL⟩:=hh; refine ⟨f+d,fun i=>?_,fun i=>⟨VerifiedReset.reg_sub (hp _).1 (hL _).1,VerifiedReset.sup_sub (hp _).1 (hL _).1 (hp _).2 (hL _).2⟩⟩ -- exits
  convert budget_plus (h i) (hD i) using 2 with j; dsimp only [Pi.add_apply]; split <;> ring

include hx hG
lemma charted : (D').beta = V'.beta+γ+ royalty W M κ d₀ (gStep V'.beta) n + heirΔ W U + mistΔ W M U X' κ d₀ k ∧
    (D').activities.E = F' + postAncestor W U + postFog W M U X' κ d₀ k:= by
  let R:= (R'); let f:= (f₀); let Z:= (s').logRead; let a:=stock W U
  have he: Z= H + (e₀) + f:= by ext i u; exact Urns.stasis (d:=d) W M U X' k u i
  obtain ⟨v,hv,hV⟩:=hx.wallet.cheap; have hy:Meadow.Budget B a.reg Z _:=⟨v,hV,fun i=>⟨hx.wallet.smooth i,hv i⟩⟩
  have hh:= minus_cost hy hx.pressure; have hz:= minus_cost hh hx.ancestry
  have hu : Z- (e₀) - H=f:=by rw [he]; abel
  rw [hu] at hz
  have hd:= detects hG hy hh; have hK:= detects hG hh hz
  have hp:= branches hG hy hh γ K₀ (T₁).clip; have hψ:= branches hG hh hz γ K₀ (T₁).clip
  have hΩ : Z-(Z-(e₀))=(e₀):= by abel
  have hY : Z-(e₀)-f=(H):=by rw [← hu]; abel
  rw [hΩ] at hp hd; rw [hY] at hK hψ
  obtain ⟨h₁,h₂,-⟩:= roll W U X' (k:=k) -- need h actual E
  have hr : δT ((R').read (s'))=δT (a.read (seed Z)):= rfl
  have h := realm W M U (κ:=κ) (d:=d)
  refine ⟨?_,?_⟩
  · rw [h₁,hr,← h.2,← show δT (a.read (seed (earnt U)))=heirΔ W U from rfl,← show δT (a.read (seed e₀)) = mistΔ W M U X' κ d₀ k from rfl,hd,hK]; unfold f; abel
  rw [(roll W U X' (k:=k)).2.2,← h.1,postFog, postAncestor,← hp,← hψ]; unfold f; abel
end YM.PhysicalNext.Repeat.Urns
