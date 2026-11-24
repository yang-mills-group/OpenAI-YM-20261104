import YM.Juniper.Bright.Security
import YM.UVExtension.Gale.Swap
/-!
 # Console interface: any boost budget in constructor pins **pre shape
 continuation** after walls, Tv F Z chosen BEFORE β growth at L_j
 configured. Important to pay on this shape for subsequent analytic RG
 estimator production. Doesn't permit asking successor geometry B_i etc.

 Adaptations ONLY construction spine; near-verbatim continue and footed from
 YM.UVExtension.Gale.Swap, new Vₓ needed. Reuse original uv_commerce
 broker for all decisions, not proof matching on another witness.
-/
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

-- shape known, but don't require restricted Germ to pay model before period
structure Booster (G:Gauge) where
  asks {X:Metals G} {D:Rolls X.p} {C:Targets X.p X.K} {L:Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (S:Register D L p v) (A:PostCost D) {P: Protection D} (W:Delays P) : Prop
  buy {X:Metals G} {D:Rolls X.p} {C:Targets X.p X.K} {L:Expenses C} {p:Return.Wages} {v:ℕ→ℝ} (S:Register D L p v) (A:PostCost D) {P: Protection D} (W:Delays P) : ∃ V:Delays P,DelayLe W V∧ asks S A V
  mono {X:Metals G} {D:Rolls X.p} {C:Targets X.p X.K} {L:Expenses C} {p:Return.Wages} {v:ℕ→ℝ} {S:Register D L p v} {A:PostCost D} {P: Protection D} {W W':Delays P} : asks S A W → DelayLe W W' → asks S A W'
def Booster.bland (G:Gauge): Booster G where
  asks _ _ _ _:= True
  buy _ _ _ T:= ⟨T,DelayLe.refl _,trivial⟩
  mono _ _:=trivial
def Booster.and (R R': Booster G): Booster G where
  asks S A _ W:= (R.asks S A W ∧ R'.asks S A W)
  buy S P _ W:= by obtain ⟨V,h,h₁⟩:=R.buy S P W; obtain ⟨T,u,h₂⟩:=R'.buy S P V; exact ⟨T,h.trans u,R.mono h₁ u,h₂⟩
  mono hh h:=⟨R.mono hh.1 h,R'.mono hh.2 h⟩

section
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : UVExtension.Case.Purchased s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
lemma juniper_continues (PB:ℕ→ℕ)(booster:Booster G): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ booster.asks R.shape A.post A.delay ∧ Juniper.Bright.Rhinestone R.target D ∧ (∀ i k,(R.expense i k).wanting= -(7/16:ℝ)) ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R k r) ∧ (UVExtension.Cloud.Leases k R.shape A.delay ∧ (∀ i j,(R.target i j).rate ≤ -(7/16:ℝ)))∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨ε,hε⟩:= UVExtension.Guild.tooling _ (show 0<UVExtension.Camp.soft from (by norm_num [UVExtension.Camp.soft,UVExtension.Oriel.rim]))
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=uv_commerce hG hh hε
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (UVExtension.Case.actualPay s T)
  obtain ⟨T',C',v,hB⟩:= pose s (UVExtension.Case.actualPay s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  obtain ⟨Λ,hΛ⟩:= UVExtension.Cloud.snow _ _ _ R E
  refine ⟨((f⊔(n⊔(L⊔v)))⊔π)⊔Λ ⊔ Juniper.Bright.floorPrice R, hr.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))), fun l he=>?_⟩
  obtain ⟨he,hPe⟩:= sup_le_iff.mp he
  obtain ⟨he,hy⟩:= sup_le_iff.mp he; obtain ⟨he,hm⟩:=sup_le_iff.mp he
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
  obtain ⟨v₉,h₉,H₉⟩:= UVExtension.Above.charts v₈ (show 0<UVExtension.Camp.soft from (by norm_num [UVExtension.Camp.soft,UVExtension.Oriel.rim]))
  obtain ⟨m,Hm⟩:= (UVExtension.Camp.delayed G hG).exists
  let w₀:Delays θ:= { v₉ with betaEntry:=fun i=>max (v₉.betaEntry i) m }
  have h₀: DelayLe v₉ w₀:= ⟨fun _=> le_max_left ..,le_rfl,le_rfl,le_rfl⟩
  obtain ⟨w₁,hw₁,hw'⟩:= UVExtension.Cloud.hones k Z w₀ (show UVExtension.Cloud.Steep G (ThroughLaunch.raise s l) _ _ Λ from hΛ) (fun i=> (hy i).trans (D.large i).need)
  obtain ⟨w₂,Hₓ,hBoost⟩:= booster.buy (X:=UVExtension.Case.provider s T l) (C:=R) Z P w₁ -- before Rooms
  obtain ⟨b,hv⟩:= hK X w₂; obtain ⟨W,hO,hQ,hX⟩:=hv J
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (h₉.trans (h₀.trans (hw₁.trans (Hₓ.trans hQ))))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hW,hU,hV,hσ⟩:= hX Y he K I a ha
  let A:Alloy (UVExtension.Case.provider s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hg:=Hₓ.trans (hQ.trans he); have hM₉:=h₀.trans (hw₁.trans hg); have hM₈:=h₉.trans hM₉; have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  obtain ⟨V,W,k,hq,hS,ha',hmT⟩:= hσ
  let F' : Factor A:=⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩
  have hA: m ≤ a.clock.bar:= by rw [ha.bar]; exact ((le_max_right _ _).trans ((hw₁.trans hg).beta _)).trans K.ready
  have hY:=UVExtension.Above.earned ha (H₉ Y hM₉) hG
  have ht':∀ i, UVExtension.Above.Entry B0.a i UVExtension.Camp.soft:= by rw [hB']; exact hY
  have hk: UVExtension.Guild.Paperwork F'.shape ε UVExtension.Camp.soft A.delay:= k
  refine ⟨hp',B0,hB',hD,F' ,rfl,rfl,hΨ,booster.mono hBoost (hQ.trans he),(Juniper.Bright.precious (G:=G) (s:=ThroughLaunch.raise s l) (K:=UVExtension.Case.actualPay s T) _ D (fun i=>(hPe i).trans (D.large i).need)),(fun i k=>(hF i k).2.2.2.1),rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩⟩, ⟨hw' Y hg,fun i j=> ((E i j).reach.le.trans_eq (hF i j|>.2.2.2.1))⟩, H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,⟨ε,UVExtension.Guild.purchase hk V W,k,hS,ha',ht', (show UVExtension.Camp.Fees B0.a from hB' ▸ Hm a hA)⟩,hq,hmT⟩

end
-- Exact continuity of choices returned.
include hG hK h
lemma juniper_footed (PB:ℕ→ℕ)(booster:Booster G): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧booster.asks R.shape A.post A.delay ∧ Juniper.Bright.Rhinestone R.target D ∧ (∀ i k,(R.expense i k).wanting= -(7/16:ℝ)) ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ (UVExtension.Cloud.Leases p R.shape A.delay ∧ (∀ i j,(R.target i j).rate ≤ -(7/16:ℝ)))∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= UVExtension.Case.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= juniper_continues hG h (h' s hS hW) PB booster
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato
