import YM.QuadraticLocal.Found.Hence
import YM.QuadraticLocal.Startup.Warm
import YM.Extension.UV.Canon.Expound
import YM.AllOrder.Transit.Tavern
import YM.AllOrder.Horizon.Order
/-!
Campaign MARKED same-beta preceptor. Uses `commercePV` retaining station choices after L before θ.
Together earns universal ordering sched request for `Legato`. Caller uses Belt & Card. This file
extends proofs of `YM/Extension/UV/Canon/Expound` and `AllOrder/Horizon/Blend` with both stations
paid & forthcoming analytic-period clauses: Kit .owns opens Rail transfer at ACTIVE
(reclosed) coupling from Cust/Marlin. It doesn't need positivity at auxiliary minimum beyond what
already learned. Room for later calendar strengthens at pre estimates keyed Support stage; for
R.Step-indexed data add one after forecast projection etc.
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

open Pressure AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal
structure WayStation {M:Metals G}{D:Rolls M.p} {A:Alloy M D}(F:Factor A):Prop where
   station : AllOrder.Transit.WheelP.Station A F
   frost : Beaming.Frost F.shape F.book F.scout A.delay
   passport : QuadraticLocal.Spes.Market.Warm A.delay

section
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : ThroughLaunch.PaidView s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
lemma expenders_R (PB:ℕ→ℕ): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R k r) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ WayStation R ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=commerce_VP hG hh
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (ThroughLaunch.bearing s T)
  obtain ⟨T',C',v,hB⟩:= pose s (ThroughLaunch.bearing s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  obtain ⟨Ω,hΩ⟩:= YM.AllOrder.Shop.leased s R E
  obtain ⟨ϕ,hΦ⟩:= YM.AllOrder.Transit.must s (ThroughLaunch.bearing s T) E z
  obtain ⟨VΞ⟩ := YM.AllOrder.Floe.Step.PlanV.acquire hG s.profile (ThroughLaunch.bearing s T) s.kernel -- args
  obtain ⟨ν,hν⟩:= VΞ.prize
  obtain ⟨ηξ,hη⟩:= YM.QuadraticLocal.Beaming.orbit R (fun i j _=> by have he:=(E i j).reach; rw [(hF i j).2.2.2.1] at he; linarith) (fun i j _=> by have he:=(E i j).worth; rw [(hF i j).2.2.1] at he; unfold rays at he; linarith [(E i j).first,(E i j).second])
  refine ⟨((f⊔(n⊔(L⊔v)))⊔π)⊔(Ω⊔(ϕ⊔(ν⊔ηξ))), hr.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)), fun l he=>?_⟩
  obtain ⟨he,Hq⟩:= sup_le_iff.mp he; obtain ⟨HΩ,Hq⟩:= sup_le_iff.mp Hq; obtain ⟨Hϕ,Hq⟩:= sup_le_iff.mp Hq; obtain ⟨Hν,Hη⟩:= sup_le_iff.mp Hq
  obtain ⟨he,hm⟩:=sup_le_iff.mp he
  obtain ⟨hf,hb⟩:=sup_le_iff.mp he; obtain ⟨hn,hv⟩:=sup_le_iff.mp hb; obtain ⟨hl,hv⟩:=sup_le_iff.mp hv
  obtain ⟨h',hp⟩:= hQ _ hf; refine ⟨h',fun D=>?_⟩; obtain ⟨w,H⟩:= hp D
  refine ⟨w,fun w' hw Q E' ξ=>?_⟩
  obtain ⟨u,Z,B,hU⟩:= H w' hw; obtain ⟨F,S,hΨ,hPocket,hZ⟩:= hU Q
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
  let M0:= ThroughLaunch.currency s T l
  have hΩ' : YM.AllOrder.Shop.Freq (s:=M0.p) E Ω:= hΩ
  have hη' : YM.QuadraticLocal.Beaming.Freq (P':=M0.p) R ηξ:= hη
  have hPz(x:ℕ): VΞ.Rise x ((D.L x).val:ℝ):= hν x (D.L x) ((Hν x).trans (D.large x).need)
  obtain ⟨Yq⟩:= Roots.options (X:=M0) D VΞ hG
  let TT i j:= (E i j).wanting
  have hTx (i j:ℕ): (E i j).wanting = -(7/16:ℝ):= (hF i j).2.2.2.1
  have hKx : AllOrder.Transit.Needed M0.p M0.K E z l := ⟨fun i j L hij hL=> hΦ.hair i j L hij ((Hϕ j).trans hL),fun j i hij L hL=> hΦ.acts j i hij L ((Hϕ j).trans hL)⟩ -- Ns
  obtain ⟨pL,hPL,HPL⟩:= AllOrder.Shop.funding (X:=M0) D Z (fun _ i=>AllOrder.Shop.edgeW i) v₈ hΩ' (fun j=>(HΩ j).trans (D.large j).need) (fun j i _=>(E j i|>.reach).trans (by rw [hTx]; norm_num)) (fun _ i=> AllOrder.Shop.edge_pp i)
  obtain ⟨pF,hPF,HPF⟩:= AllOrder.Transit.predicts (X:=M0) Z VΞ Yq z C (rays s) mile p₁ S (wind X) hG hKx (fun i j _=>(hF i j).1) (fun i j _=>hTx i j) (fun i j _=> by unfold rays; linarith [(s.profile j).price_pos]) hϑ pL
  obtain ⟨pS,hPS,HPS⟩:= Roots.summit (X:= M0) D VΞ hPz Yq pF
  obtain ⟨pB,hPB,HPB⟩:= demands (X:=M0) pS
  obtain ⟨pZ,hz0,hZ0⟩:= YM.QuadraticLocal.Beaming.option Z F S hPocket hη' (fun j=>(Hη j).trans (D.large j).need) pB
  obtain ⟨pW,hPw,HW⟩:= QuadraticLocal.Spes.Market.accrue pZ
  let W' := hPL.trans (hPF.trans (hPS.trans (hPB.trans hz0)))
  obtain ⟨b,hv⟩:= hK X pW; obtain ⟨W,hO,hQw,hX⟩:=hv J
  let hQ:= hPw.trans hQw
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (W'.trans hQ)))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hW,hU,hV,hϑ',hσ⟩:= hX Y he K I a ha
  let A:Alloy (ThroughLaunch.currency s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hM₈:=W'.trans (hQ.trans he); have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  refine ⟨hp',B0,hB',hD, ⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩,rfl,rfl,hΨ,rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩⟩,H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,⟨⟨VΞ,Yq,⟨HPF _ (hPS.trans (hPB.trans (hz0.trans (hQ.trans he)))), ⟨hPz,HPS _ (hPB.trans (hz0.trans (hQ.trans he))),HPL _ (hPF.trans (hPS.trans (hPB.trans (hz0.trans (hQ.trans he))))), hϑ', hσ⟩⟩, HPB _ (hz0.trans (hQ.trans he)) ⟩,hZ0 _ (hQ.trans he), HW _ (hQw.trans he)⟩,hσ⟩ -- type. handbook

end
-- Exact continuity of choices returned.
include hG hK h
lemma ruese_R (PB:ℕ→ℕ): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ WayStation R ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= ThroughLaunch.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= expenders_R hG h (h' s hS hW) PB
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato

