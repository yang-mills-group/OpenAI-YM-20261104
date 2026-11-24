import YM.LocalLTE.Cycles.Day
/-! ballot purchase AFTER delays otherwise chosen; any chronology. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.ClockB
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Height Roof Trio YM.LocalLTE.Inset
variable {G : Gauge} {c f : Side} {j i k n m a : ℕ} {X:Metals G} (D:Rolls X.p) {C:Targets X.p X.K} {Z: Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (R:Register D Z p v) {F:ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {P:Protection D}
structure Wind (p : ℕ) (η:ℝ) where
  l : ℝ -- Song T
  w : ℝ -- cone slim
  u : ℝ -- cone trimmed
  q : ℝ -- Aero authority
  e : ℝ -- final comparison
  ℓ : ℕ -- entropy stitch price
  oak : - (1/2:ℝ) < u
  oak' : u < w
  cedar : w < vow
  κ : 1+w*(p+3:ℝ) < l
  hemlock : l < e
  minister : e = -((p:ℝ)+1-η) / 2
  ore : q ≤ l
  fur : q < -(23/20:ℝ)
  mars : 3 ≤ ℓ
  legs : -(3/8:ℝ)*(ℓ-3:ℕ) < q
lemma airborne (p:ℕ){η:ℝ}(he:0<η) : Nonempty (Wind p η):= by
  obtain ⟨w,h,h',hy⟩:= within p η he
  obtain ⟨l,hl,hL⟩:= exists_between hy
  let f:=min (-2:ℝ) l
  obtain ⟨z,hz⟩:= exists_nat_gt ((-(8/3:ℝ))*f)
  obtain ⟨u,hu,hU⟩:=exists_between h
  refine ⟨⟨l,w,u,f,_,3+z,hu,hU,h',hl,hL,rfl,min_le_right ..,?_,by omega,?_⟩⟩
  · linarith only [show f≤-2 from min_le_left ..]
  rw [Nat.add_sub_cancel_left]; linarith only [hz]
variable {p' ℓ:ℕ} {w l q α κ Y₀ η : ℝ}

def height (ℓ:ℕ) (x i:ℕ) := Trio.resize ℓ (C x i|>.halo)
abbrev vista (ℓ x i:ℕ) (t:ℝ) : ℝ := paySide G (D.L x) (height (C:=C) ℓ x i) t
variable (W:Wind p' η)
-- all outside pointwise over x. h : Steps even schedule? no
set_option quotPrecheck false
structure Currencies (j i:ℕ) (κ d x : ℝ) : Prop where
  aero : Height.Aerobics (Z j i) (D.L j) (p j i) (R.μ j i) (R.c j i) (R.o j i) x W.q (heap G (X.p.profile i) (1/16)) W.ℓ (X.p.profile i).order (X.p.profile i).power Chi.canonical
  coat : ∀ z:BudgetPoint,z.threshold ≤ 2*Pressure.fiery G x (D.L j)→z.power=(X.p.profile i).power→z.order=(X.p.profile i).order→z.supportExponent=(X.p.profile i).supportExponent→z.B= radiusB x→∀ β a Λ:ℝ,|β| ≤2*betaF G x (D.L j)→|a|≤cloak D j→0 ≤Λ→Λ≤ ConnectedActivityE6.loopBill G (D.L j) x →
    let P:=X.p.profile i
    Real.exp (-(P.width/4)*z.B) *Song.octaveNeed G z P.clip P.width P.paths Λ β a ≤betaF G x (D.L j) ^ W.q
  wake : Waking D R (vista D (C:=C) W.ℓ) i j (p'+(X.p.profile i).order) p' W.w W.l d x
  light : let y:= betaF G x (D.L j); let Z:=X.p.profile i; let L:=D.L j; let b:=height (C:=C) W.ℓ j i; let s:= lanternPay G L Z W.q x
          1≤ y ∧ s≤gold G L x ∧ s+Height.away Z * (planks G L b Z x * Real.exp (stout Z * coverTicket b)) ≤ gapB G Z x ∧ tomorrow G L Z b W.l W.q x ≤ y^W.e
  tithe : let b:=height (C:=C) W.ℓ j i; let σ:=X.p.profile i; let L:=D.L j
          Marlin.tithe (2*base b (radiusB x)) (lossFee G L (Z j i).wanting b σ x) ⟨σ.power,σ.order, σ.supportExponent,1,1,σ.power_ge,σ.order_ge,σ.price_pos,Nat.zero_lt_one,zero_lt_one,le_rfl⟩ (coverTicket b) ≤ betaF G x L ^(-(1/8):ℝ)
  frame : ∀ (P:BudgetPoint), P.threshold ≤ 2*Pressure.fiery G x (D.L j) → let d':=YM.LocalLTE.Inset.cone W.u (betaF G x (D.L j))
          let f:= height (C:=C) W.ℓ j i; let h:=Trio.base f (radiusB x); let r:= fence f (radiusB x)
          ∀ c:Side, 2*h<c.val→∀ o:Site c,∀ V: Config G c, Healthy P.threshold (neighbors h o) V→ ∀ i:Stars, ∃ (u:Site (r i)→G.El) (z: Positions (Uniform.Primary (r i) G)), actual z=gauge u (Slide.shape (Trio.pad (w:=tent f (radiusB x)) (fun l:Stars=> (show (r l).val=2*(tent f (radiusB x)+l.val) from rfl)) i) o V) ∧ ‖z‖+2*Sienna.furl G (D.L j) x<d'
  books : let L:=D.L j; let b:=height (C:=C) W.ℓ j i; let k:= (X.p.profile i).order
          ∀ s:Stars,YM.LocalLTE.Frame.Lease G k κ (Trio.fence b (radiusB x) s) (cone W.w (betaF G x L)) (cone W.u (betaF G x L)) Chi.canonical
  tears : YM.LocalLTE.Frame.Tears G (D.L j) (X.p.profile i).order W.u x
-- Bring d BEFORE β
variable {d:ℕ→ℕ→ℝ}
lemma assay (j i:ℕ) (h: StepStages j i) (hv: (Z j i).wanting= -(7/16:ℝ)) (hL:(Height.aerodynamic (C j i)).choose ≤ (D.L j).val) (hq: Reliable G κ q) :
   ∃ b:ℝ,0<b ∧ ∀ᶠ x in atTop, Currencies D R W j i κ b x:= by
  let t:= height (C:=C) W.ℓ j i; let L:= D.L j; let P:= X.p.profile i
  obtain ⟨b,hb,he⟩:= Pane.woke D R (vista D (C:=C) W.ℓ) h (show p'≤p'+(X.p.profile i).order by omega) (W.oak.trans W.oak') W.cedar W.κ (show Bolt G L (fun x=> paySide G L t x) from Trio.circles ..)
  refine ⟨b,hb,?_⟩; have hk:= medium D R (1/16) hL W.mars W.legs h
  filter_upwards [hk,flight D R W.q hv.le h, he, ClockB.spritely G L P t W.l W.q W.fur W.ore W.hemlock, Trio.cheap G L _ t P hv, Trio.frames_fields G L W.ℓ (C j i|>.halo) W.u W.oak, ClockB.frameBook D (C:=C) W.oak' (W.cedar.trans vow_ok) hq j i W.ℓ, YM.LocalLTE.Frame.admits G L P.order W.oak (W.oak'.trans W.cedar)] with x hf hg ho hu hp hm hx hB using ⟨hf,hg,ho,hu,hp,hm,hx,hB⟩
-- pay Gold authority from Pane.Morning with N patch
variable (A:PostCost D)
structure Spoke (κ:ℝ) (d:ℕ→ℕ→ℝ) (V:Delays P): Prop where
  cash j i (h:StepStages j i): 0 < d j i ∧ ∀ x≥V.betaEntry j,Currencies D R W j i κ (d j i) x
  golds : Pane.Planks D R A (vista D (C:=C) W.ℓ) V (fun _ i=> (X.p.profile i).order)
  shells j i (h:StepStages j i) : Trio.maxFixed (height (C:=C) W.ℓ j i) ≤ V.shells j
  stages j i (h:StepStages j i) : 1≤ V.growth j
lemma forever (hq:Reliable G κ q) (h : ∀ j i, StepStages j i→ (Z j i).wanting=-(7/16:ℝ)) (ht:∀ j i,StepStages j i→(Height.aerodynamic (C j i)).choose≤(D.L j).val):
    ∃ d:ℕ→ℕ→ℝ,∀ V:Delays P,∃ W':Delays P,DelayLe V W'∧∀ U: Delays P, DelayLe W' U → Spoke D R W A κ d U:= by
  have hx j i:∃ b:ℝ,0<b∧∀ᶠ x in atTop,StepStages j i→ Currencies D R W j i κ b x:= by
    by_cases he : StepStages j i
    · obtain ⟨p,hp,hx⟩:= assay D R W _ _ he (h _ _ he) (ht _ _ he) hq; exact ⟨p,hp,hx.mono fun _ hh _=>hh⟩
    exact ⟨1,zero_lt_one,by simp [he]⟩
  choose d hb hD using hx
  refine ⟨d,fun V=>?_⟩
  obtain ⟨V',hv,hP⟩:= Pane.school D R A (vista D (C:=C) W.ℓ) (fun _ i=> (X.p.profile i).order) (fun j i hi=> le_trans (by decide : 2≤6) (X.p.profile i).order_ge) (fun j i h=>Trio.circles ..) V
  obtain ⟨x,-,hp,hv'⟩:= collect_upper V'.betaEntry _ fun j=>eventually_transitions j _ _ fun i (he:StepStages j i)=> ((hD _ _).mono fun _ h=>h he)
  let u' j i:= Trio.maxFixed (height (C:=C) W.ℓ j i)
  let k:Delays P := {V' with betaEntry:=x, shells:=fun i=> V'.shells i+ fromMax u' i, growth:=fun i=> V'.growth i + 1}
  let H: DelayLe V' k:=⟨hp,le_rfl,fun i=> Nat.le_add_right ..,fun i=> Nat.le_succ _⟩
  exact ⟨k,hv.trans H,fun U h=>⟨fun j i hi=> ⟨hb j i,fun t ht=> hv' j _ ((h.beta _).trans ht) i hi⟩, hP _ (H.trans h), fun j i hi=> ((le_fromMax u' hi).trans (Nat.le_add_left (fromMax _ _) _)).trans (h.shells _),fun j i hi=>(Nat.le_add_left 1 _).trans (h.growth _)⟩⟩
end YM.PhysicalNext.Repeat.ClockB
