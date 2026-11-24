import YM.UVExtension.Gale.Swap
/-! # PostHeight oriented requests (pass one `Assembled` result to all clients).
 Supports both pre-L and after-L payments (P⌇a.K.C attached). Other data needed billed elsewhere.
 Keeps Oculus.Rate.There costs (ζ not assuming buys on every A.Family). No reset law claim here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Witness
open Filter Function Lattice RG Supply Wilson Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Roof PhysicalNext.Repeat.Roost
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open MeasureTheory Push.PriceCompiler Input Org UVExtension
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
-- Rough authority. Meets requests if able on BARE Registers BEFORE adding further after-L forecasts. Keep superspec.Omega. No claims at higher order etc.
structure Rewards (G:Gauge) where
   rule {s:Sheet G} (K:MapPrices) {C:Targets s K} (E:Expenses C) {D:Rolls s} (S:PostCost D) {w:Return.Wages} {a:ℕ→ℝ} (Y: PhysicalNext.Repeat.Register D E w a) {F:ℕ→ℕ→Postage} (U: Time.Scouts (F:=F)){T: Protection D}(W:Delays T): Prop

-- keep standard size choices as cheap hypotheses
abbrev jewell {s:Sheet G}{K:MapPrices}{C:Targets s K}(E: Expenses C): Prop:=∀ i k,(C i k).table=Next.Foundations.chart G ∧ (C i k).halo=500∧ (E i k).earn=Roof.rays s i k∧ (E i k).wanting=-(7/16:ℝ)∧(E i k).degrees=0

def Encounters (J: Rewards G): Prop:=∀ (s:Sheet G) (K:MapPrices) (C:PhysicalNext.Repeat.Targets s K)(E:Expenses C), jewell E→∃ v:ℕ→ℕ, ∀ L, v ≤ L→ ∀ (D:Rolls (ThroughLaunch.raise s L))(P:PostCost D)(w:Return.Wages) (a:ℕ→ℝ)(R: PhysicalNext.Repeat.Register D E w a)(F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F))(T:Protection D)(V:Delays T),∃ W:Delays T,DelayLe V W ∧∀ Y:Delays T, DelayLe W Y → J.rule (s:=ThroughLaunch.raise s L) K E P R S Y

def permits (J:Rewards G){M:Metals G}{D:Rolls M.p}{B:Alloy M D}(R:Factor B): Prop:= J.rule M.K R.expense B.post R.shape R.scout B.delay
lemma pairs {u v: Rewards G} (hx:Encounters u)(hy:Encounters v): ∃ w:Rewards G, Encounters w ∧ ∀ (M:Metals G)(D:Rolls M.p)(B:Alloy M D)(R:Factor B), permits w R → permits u R ∧ permits v R:=by
   let w: Rewards G:=⟨fun {_} K {_} E {_} p {_} {_} r {_} s {_} X=> u.rule K E p r s X ∧ v.rule K E p r s X⟩ -- implicit binder names
   refine ⟨w,?_,fun _ _ _ _ h=>h⟩
   intro s K C E h; obtain ⟨L,hx⟩:= hx s K C E h; obtain ⟨B,hy⟩:=hy s K C E h; refine ⟨L⊔B,fun F h D P w' b Y O Z t V=>?_⟩; obtain ⟨T,hT,hV⟩:= hx F (le_sup_left.trans h) D P w' b Y O Z t V; obtain ⟨W,hW,h'⟩:= hy F (le_sup_right.trans h) D P w' b Y O Z t T; exact ⟨W,hT.trans hW,fun V hv=>⟨hV V (hW.trans hv),h' V hv⟩⟩
abbrev nullR (G:Gauge): Rewards G:=⟨fun {_} _ {_} _ {_} _ {_} {_} _ {_} _ {_} _=>True⟩
lemma minimum : Encounters (nullR G):=fun _ _ _ _ _=>⟨0,fun _ _ _ _ _ _ _ _ _ _ V=> ⟨V,DelayLe.refl V,fun _ _=> trivial⟩⟩
end YM.RGComparison.Core16.Witness

namespace YM.PhysicalNext.Repeat.Legato.Core16
/-!
# Extend Gale/Swap source purchase to be able to pay the Core16 strong-post requests. Keep all existing Burn requirements (even if unclaimed yet by cp6 workers). Availability before order legs. Need separate Flora spring assumption purchased afterward.
-/
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
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : UVExtension.Case.Purchased s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
lemma continues_rewarded (J₁ : RGComparison.Core16.Witness.Rewards G)(hJ : RGComparison.Core16.Witness.Encounters J₁)(PB:ℕ→ℕ): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ RGComparison.Core16.Witness.permits J₁ R ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R k r) ∧ (UVExtension.Cloud.Leases k R.shape A.delay ∧ (∀ i j,(R.target i j).rate ≤ -(7/16:ℝ)))∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨ε,hε⟩:= UVExtension.Guild.tooling _ (show 0<UVExtension.Camp.soft from (by norm_num [UVExtension.Camp.soft,UVExtension.Oriel.rim]))
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=uv_commerce hG hh hε
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (UVExtension.Case.actualPay s T)
  obtain ⟨T',C',v,hB⟩:= pose s (UVExtension.Case.actualPay s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  obtain ⟨Λ,hΛ⟩:= UVExtension.Cloud.snow _ _ _ R E
  obtain ⟨Λplus,hΛplus⟩:= hJ _ (UVExtension.Case.actualPay s T) R E hF
  refine ⟨((f⊔(n⊔(L⊔v)))⊔π)⊔(Λ⊔Λplus), hr.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)), fun l he=>?_⟩
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
  obtain ⟨w₁,hw₁,hw'⟩:= UVExtension.Cloud.hones k Z w₀ (show UVExtension.Cloud.Steep G (ThroughLaunch.raise s l) _ _ Λ from hΛ) (fun i=> ((le_sup_left.trans hy) i).trans (D.large i).need)
  obtain ⟨w₁plus,hwP,hPplus⟩:= hΛplus l (le_sup_right.trans hy) D P w' u Z F S θ w₁
  obtain ⟨b,hv⟩:= hK X w₁plus; obtain ⟨W,hO,hQ,hX⟩:=hv J
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (h₉.trans (h₀.trans (hw₁.trans (hwP.trans hQ))))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hW,hU,hV,hσ⟩:= hX Y he K I a ha
  let A:Alloy (UVExtension.Case.provider s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hg:=hwP.trans (hQ.trans he); have hM₉:=h₀.trans (hw₁.trans hg); have hM₈:=h₉.trans hM₉; have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  obtain ⟨V,W,k,hq,hS,ha',hmT⟩:= hσ
  let F' : Factor A:=⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩
  have hA: m ≤ a.clock.bar:= by rw [ha.bar]; exact ((le_max_right _ _).trans ((hw₁.trans hg).beta _)).trans K.ready
  have hY:=UVExtension.Above.earned ha (H₉ Y hM₉) hG
  have ht':∀ i, UVExtension.Above.Entry B0.a i UVExtension.Camp.soft:= by rw [hB']; exact hY
  have hk: UVExtension.Guild.Paperwork F'.shape ε UVExtension.Camp.soft A.delay:= k
  refine ⟨hp',B0,hB',hD,F' ,rfl,rfl,hΨ, hPplus Y (hQ.trans he), rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩⟩, ⟨hw' Y hg,fun i j=> ((E i j).reach.le.trans_eq (hF i j|>.2.2.2.1))⟩, H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,⟨ε,UVExtension.Guild.purchase hk V W,k,hS,ha',ht', (show UVExtension.Camp.Fees B0.a from hB' ▸ Hm a hA)⟩,hq,hmT⟩

end
-- Exact continuity of choices returned.
include hG hK h
lemma footed_rewarded (J₁ : RGComparison.Core16.Witness.Rewards G)(hJ : RGComparison.Core16.Witness.Encounters J₁)(PB:ℕ→ℕ): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧ RGComparison.Core16.Witness.permits J₁ R ∧R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ (UVExtension.Cloud.Leases p R.shape A.delay ∧ (∀ i j,(R.target i j).rate ≤ -(7/16:ℝ)))∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= UVExtension.Case.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= continues_rewarded hG h (h' s hS hW) J₁ hJ PB
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato.Core16
