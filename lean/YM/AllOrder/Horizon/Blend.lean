import YM.AllOrder.Plateau.Horizon
import YM.TraceExtension.Made.Exp
/-! # Join Pledge in the original TraceExtension interface tier (version of trace/Exp) -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Shop
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext Repeat Height Song Geo RG.Shoot
open Push.Uniform Blaze Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X: Metals G} (D: Rolls X.p) {C : Targets X.p X.K} {Z :Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (R : Repeat.Register D Z p v)
   {P : Protection D} (A : PostCost D)

abbrev Pledged {D:Rolls X.p} (A:Alloy X D) (F:Factor A):= Shop.Lodge D F.shape (fun _ i=> Shop.edgeW i) A.delay ∧ Shop.Fair D F.target A.delay ∧ Shop.Snow D F.shape A.post A.delay ∧ Plateau.Line.Reserve D F.target A.delay
lemma budgetH (V:Delays P) {u:ℕ→ℕ} (h: Freq Z u) (hp : ∀ j,u j ≤ (D.L j).val) (hq : ∀ i j,(Z i j).wanting= -(7/16:ℝ)) (hG:G.Simple): ∃ W:Delays P,DelayLe V W ∧ ∀ Y: Delays P, DelayLe W Y → Lodge D R (fun _ i=> Shop.edgeW i) Y ∧ Fair D C Y ∧ Snow D R A Y ∧ Plateau.Line.Reserve D C Y:= by
  obtain ⟨X₁,h₁,hP⟩:= Shop.funding D R (fun _ i=> Shop.edgeW i) V h hp (fun j i _=> lt_trans (Z j i|>.reach) (by rw [hq]; norm_num)) (fun _ i=> Shop.edge_pp i)
  obtain ⟨X₂,h₂,hU⟩:= Shop.budget_extra D R A X₁ (fun j i _=> hq j i)
  obtain ⟨X₃,h₃,hF⟩:= Shop.climb D C X₂
  obtain ⟨X₄,h₄,hπ⟩:= Plateau.Line.gift D C X₃ hG
  exact ⟨X₄,h₁.trans (h₂.trans (h₃.trans h₄)),fun _ h=>⟨hP _ (h₂.trans (h₃.trans (h₄.trans h))), hF _ (h₄.trans h),hU _ (h₃.trans (h₄.trans h)),hπ _ h⟩⟩
end YM.AllOrder.Shop
end

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple) {K : KernelChoices} (hK : ∀ p:Patch,p.Branches K G)
    (v : ThroughLaunch.Orders) (h : ThroughLaunch.Draft v)

section
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : ThroughLaunch.PaidView s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
-- written with extra gates after mapping Calendar:
lemma expendersH (PB:ℕ→ℕ): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, AllOrder.Shop.Pledged A R ∧ R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ R.menu=H∧ R.auxiliary=J ∧ (∃ b:Bandage R k r, Quince.Skill b (Quince.bear r)) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=commerce hG hh
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (ThroughLaunch.bearing s T)
  obtain ⟨T',C',v,hB⟩:= pose s (ThroughLaunch.bearing s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  obtain ⟨κ,hκ⟩:= YM.AllOrder.Shop.leased s R E
  refine ⟨((f⊔(n⊔(L⊔v)))⊔κ)⊔π, hr.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)), fun l he=>?_⟩
  obtain ⟨he,hm⟩:=sup_le_iff.mp he; obtain ⟨he,hΩ⟩:=sup_le_iff.mp he
  obtain ⟨hf,hb⟩:=sup_le_iff.mp he; obtain ⟨hn,hv⟩:=sup_le_iff.mp hb; obtain ⟨hl,hv⟩:=sup_le_iff.mp hv
  obtain ⟨h',hp⟩:= hQ _ hf; refine ⟨h',fun D=>?_⟩; obtain ⟨w,H⟩:= hp D
  refine ⟨w,fun w' hw Q E' ξ=>?_⟩
  obtain ⟨u,Z,B,hU⟩:= H w' hw; obtain ⟨F,S,hΨ,hZ⟩:= hU Q
  obtain ⟨q,η,P,hp⟩:=hZ E' ξ; refine ⟨P,fun θ₀ hθ=>?_⟩
  obtain ⟨θ,hα,p₁,hϑ,hK⟩:= hp _ hθ
  obtain ⟨M,hP,H⟩:=cymbals D (retune (u:=l) hB) hv (fun _ _=> 1/4) (fun _ _=> by norm_num)
  refine ⟨θ,hα,fun X V J=>?_⟩
  obtain ⟨V₁,hv₁,hP₁⟩:= Mallow.brevity Z (show Mallow.Arena (ThroughLaunch.raise s l) _ _ _ n from hA) (fun j=>(hn j).trans (D.large j).need) V
  obtain ⟨V₂,hv₂,hP₂⟩:= Graces.reacts (s:=ThroughLaunch.raise s l) C D p₁ mile Z V₁ hϑ
  obtain ⟨V₃,hv₃,hP₃⟩:= Circlet.chords (M:=ThroughLaunch.raise s l) C' D M mile Z hP V₂
  obtain ⟨V₄,hv₄,hP₄⟩:= H θ V₃
  obtain ⟨V₅,hv₅,hP₅⟩:= Graces.compass Z V₄
  obtain ⟨V₆,hv₆,hP₆⟩:= Cub.motions (M:=ThroughLaunch.raise s l) R E mile D Z C' M hP V₅
  obtain ⟨v₇,hv₇,H₇⟩:= Mallow.scarce Z PB V₆
  obtain ⟨v₈,h₈,H₈⟩:= Mallow.swelling Z PB v₇
  obtain ⟨vC,hj,hc₁⟩:= Quince.parliament Z C' M mile (Quince.bear r) (Quince.bear_pos r) hP v₈
  let M0:= ThroughLaunch.currency s T l
  have hν : YM.AllOrder.Shop.Freq (s:=M0.p) E κ:= hκ
  obtain ⟨vK,hz₀,hK₀⟩:= YM.AllOrder.Shop.budgetH (X:=M0) D Z P vC hν (fun j=>(hΩ j).trans (D.large j).need) (fun i j=>hF i j |>.2.2.2.1) hG
  obtain ⟨b,hv⟩:= hK X vK; obtain ⟨W,hO,hQ,hX⟩:=hv J
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (hj.trans (hz₀.trans hQ))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hW,hU,hV,hσ⟩:= hX Y he K I a ha
  let A:Alloy (ThroughLaunch.currency s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hM₈:=hj.trans (hz₀.trans (hQ.trans he)); have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  refine ⟨hp',B0,hB',hD, ⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩,hK₀ Y (hQ.trans he),rfl,rfl,hΨ,rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩, hc₁ Y (hz₀.trans (hQ.trans he))⟩,H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,_,hσ.choose_spec⟩

end
-- Exact continuity of choices returned.
include hG hK h
lemma rueseH (PB:ℕ→ℕ): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,AllOrder.Shop.Pledged A R ∧ R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ (∃ b:Bandage R p W, Quince.Skill b (Quince.bear W)) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= ThroughLaunch.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= expendersH hG h (h' s hS hW) PB
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato
