import YM.LocalLTE.Vinca.Trip
import YM.Qlocal.Prism
/-! Pay an arbitrary represented-density program before selecting the C18
funding and directed factor. This follows the C18 construction in Vinca.Wreath,
retaining the register pocket and the kinetic archive through Qlocal.Prism. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
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
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {O₀:ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : ThroughLaunch.PaidView s O T p h k r f t v₀) (hC : Chop s O₀ mile)
open YM.Qlocal.Schedule
variable {Hgoal : Goal G} (buy : Obtainable Hgoal)
include hh hC hG buy
theorem jointFunding (U:Mallow.Prereq G) (p0 τ:ℕ){ε δ:ℝ}(hε: δ<ε)(Wt : ClockB.Wind p0 δ)(hr:Wt.l < LocalLTE.Fan.Pastel.chip (τ+1)) (PB:ℕ→ℕ)(d0:ℕ→ℕ→ℕ)(TT:ℕ)(Γ:ℝ)(hU0:0<Γ)(hLu:Γ<(τ:ℝ)/100)(Ft:Mallow.Involve G τ TT Γ d0 ) (lH:ℕ)(hG2:∀ i, 1≤O₀ i ∧ O₀ i≤ k i)(hGt:∀ j i, StepStages j i → tabP lH (s.profile i|>.supportExponent)*O₀ j+1 ≤ k j)(Fζ:Elixir G τ): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.bearing s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.currency s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R O₀ r)∧ Elevates B.a O₀ r lH ∧ (∀ i j,(R.target i j).halo=500) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ (∃ (M:Mallow.Funding R p0 ε)(W:Mallow.Trail M τ)(_:Mallow.Adorn M W), Mallow.Cready M W∧ U.jobs A.delay M.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target τ Γ,Mallow.Bouquets R.shape Z M.κ d0 TT A.delay ∧ Mallow.SuppliesQ M W Z Ft∧Fulfilled Fζ M W) ∧ Hgoal _ _ A R ∧ Extension.UV.Archive B ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨f,C,z,R,E,bt,hT,hF,hQ⟩:=commerceP hG hh
  obtain ⟨floor,offered⟩ := buy s T C z R E hF
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (ThroughLaunch.bearing s T)
  obtain ⟨T',C',v,hB⟩:= pose s (ThroughLaunch.bearing s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  let Xg:= Push.PriceCompiler.fromMax (ClockB.capline (s:=s) (K:=ThroughLaunch.bearing s T) R)
  have hu : ∀ j i,(R j i).rate< LocalLTE.Fan.Pastel.mini:=by
     intro j i; apply (E j i).reach.trans; rw [(hF j i).2.2.2.1]; norm_num [LocalLTE.Fan.Pastel.mini]
  obtain ⟨γ,r₀,hLam,hRel⟩:= ConnectedActivityE6.reliable G
  obtain ⟨f₀,F'₀,m₀,ψ,μ,hζ,hK₀⟩:= Mallow.ether s T τ Wt R E z (hRel _ hLam le_rfl) hu
  have hR :∀ i j, 3/8+(R i j).rate< Mallow.aust:= by
     intro i j; have he:=(E i j).reach; rw [(hF i j).2.2.2.1] at he; unfold Mallow.aust; linarith
  obtain ⟨Zs,hWZ,hzR⟩:= Mallow.Wickets.springT d0 R E hR r₀ (hRel _ hLam le_rfl) hU0 hLu TT
  obtain ⟨F₁,hF'⟩:= affordsExtra s lH (fun i=> (hG2 i).1) hGt
  obtain ⟨F₂,hF₂⟩:= Fζ.pays R E (fun i j=>⟨(hF i j).2.1,(hF i j).2.2.2.1⟩) r₀ _ (hRel _ hLam le_rfl)
  let original := (F₁⊔F₂)⊔(((Xg⊔f₀)⊔hWZ)⊔((f⊔(n⊔(L⊔v)))⊔π))
  have old : v₀ ≤ original := hT.trans (((le_sup_left.trans le_sup_left).trans le_sup_right).trans le_sup_right)
  refine ⟨original ⊔ floor, old.trans le_sup_left,fun l budget=>?_⟩
  obtain ⟨he,hfloor⟩ := sup_le_iff.mp budget
  obtain ⟨hc,he⟩:=sup_le_iff.mp he; obtain ⟨hc,hA1⟩:=sup_le_iff.mp hc
  obtain ⟨hw₁,he⟩:= sup_le_iff.mp he; obtain ⟨hw₀,hw₂⟩:= sup_le_iff.mp hw₁
  obtain ⟨he,hm⟩:=sup_le_iff.mp he
  obtain ⟨hf,hb⟩:=sup_le_iff.mp he; obtain ⟨hn,hv⟩:=sup_le_iff.mp hb; obtain ⟨hl,hv⟩:=sup_le_iff.mp hv
  obtain ⟨h',hp⟩:= hQ _ hf; refine ⟨h',fun D=>?_⟩; obtain ⟨w,H⟩:= hp D
  refine ⟨w,fun w' hw Q E' ξ=>?_⟩
  obtain ⟨u,Z,B,hU⟩:= H w' hw; obtain ⟨F,S,hΨ,pocket,hZ⟩:= hU Q
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
  let Y₀:= Wt
  let A₀:= ThroughLaunch.currency s T l; obtain ⟨hx,h₀⟩:= sup_le_iff.mp hw₀
  obtain ⟨d,hf⟩:= ClockB.forever (P:=θ) (X:=A₀) D Z Y₀ P (hRel _ hLam le_rfl) (fun j i _=> (hF j i).2.2.2.1) (fun i j h=> Push.PriceCompiler.le_fromMax (ClockB.capline R) h|>.trans ((hx i).trans (D.large i).need))
  obtain ⟨v₉,h₉,H₉⟩:=hf v₈
  obtain ⟨Va,hτ,hω⟩:= Urns.balances (X:=A₀) D P p0 Y₀.e ε (by rw [Y₀.minister]; linarith) v₉
  obtain ⟨hp₀,hPβ,hΨ',hG',g₁,hS,hW⟩:= hK₀ l h₀ D
  let N:= Mallow.bsize s T Y₀ R
  have hK₁:= H₉ Va hτ
  obtain ⟨X₁,hX₁,hK₂⟩:= Coup.shines (κ:=r₀) (X:=A₀) Y₀ D Z m₀ ψ N τ (fun i j _=> hu i j) (fun i j=> (hζ i j).1) hΨ' (Y₀.ore.trans_lt hr) hS hW hG' Va -- order edit
  obtain ⟨X₂,hX₂,hK₃⟩:= Roof.pewsT (s:= ThroughLaunch.raise s l) z (Roof.rays s) C p₁ mile Z (Roof.wind X) hG m₀ (fun i j=> (hζ i j).1) hPβ hϑ (fun i j=>by unfold Roof.rays; linarith [(s.profile j).price_pos]) X₁
  obtain ⟨M',X₃,hX₃,hK₄⟩:= Mallow.verdant s T τ Wt R E (κ:=r₀) (hRel _ hLam le_rfl) D Z d F'₀ ψ μ (fun i j h=> (hK₁.cash i j h).1) hr (fun i j=>(hζ i j).2) X₂ -- order
  obtain ⟨X₄,hX₄,hM₀⟩:= Mallow.dealsK Z N ψ X₃
  let Ys:= ThroughLaunch.raise s l; let Rt:Targets Ys (ThroughLaunch.bearing s T):= R
  let Zt:Mallow.Wickets Rt τ Γ:= ⟨Zs.degree,fun i=> ⟨(Zs.tuner i).azi,(Zs.tuner i).kap,(Zs.tuner i).bbase,(Zs.tuner i).amp,(Zs.tuner i).strength,(Zs.tuner i).bill⟩⟩
  have hX5 : Mallow.Wickets.Harvest Rt E Zt r₀ d0 TT hWZ:= ⟨⟨hzR.stalk.start, hzR.stalk.side,hzR.stalk.power,hzR.stalk.pinch⟩,hzR.star⟩
  obtain ⟨X₅,hX₅,hM₁⟩:= Mallow.flowersT d0 Z Zt r₀ hX5 (fun i=> (hw₂ i).trans (D.large i).need) X₄
  obtain ⟨X₆,hX₆,hM₂⟩:= U.buys X₅ r₀ ⟨_,hRel _ hLam le_rfl⟩
  obtain ⟨X₇,hX₇,hX₇'⟩:= (Ft.annual p0 _ Wt).buys (X:=A₀) Z d r₀ _ N N F'₀ Zt X₆ (hRel _ hLam le_rfl) (fun i j h=> (hK₁.cash i j h).1) (hM₁ _ hX₆) -- sorted d
  obtain ⟨X₈,hX₈,H₈'⟩:= hF₂ l hA1 D Z N F'₀ X₇
  obtain ⟨X₉,h₉',grant⟩ := offered l hfloor D w' u Z F S pocket p₁ hϑ θ X X₈
  obtain ⟨b,hv⟩:= hK X X₉; obtain ⟨W,hO,issued,hX⟩:=hv J
  have hQ := h₉'.trans issued
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (h₉.trans (hτ.trans (hX₁.trans (hX₂.trans (hX₃.trans (hX₄.trans (hX₅.trans (hX₆.trans (hX₇.trans (hX₈.trans hQ))))))))))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc1,hD,hp',B0,hB',hf,hW,hU,hV,archive,hσ⟩:= hX Y he K I a ha
  let A:Alloy (ThroughLaunch.currency s T l) D:= Alloy.mk P θ Y K I hp' B0
  have he8:=hQ.trans he; have he7:= hX₈.trans he8; have he6:= hX₇.trans he7; have he5:=hX₆.trans he6; have he4:=hX₅.trans he5; have he3:=hX₄.trans he4; have he2:= hX₃.trans he3; have he1:= hX₂.trans he2; have he0:= hX₁.trans he1
  have hN:=(hτ.trans he0); have hM₈:= h₉.trans hN; have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  let R₀:Roost.Factor A:= ⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩
  have grantR : Hgoal _ _ A R₀ := grant Y (issued.trans he) P K I hp' B0 archive hσ
    E' η q B bt b J hf (fun i j => (hF i j).1) hW (hB'.symm ▸ hp)
  let F₀ :Mallow.Funding R₀ p0 ε:= ⟨_,Wt,r₀,d,⟨_,hRel _ hLam le_rfl⟩,H₉ Y hN,hω Y he0⟩
  refine ⟨hp',B0,hB',hD, R₀,rfl,rfl,hΨ,rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ thinner hc1 hG2,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩⟩, hB'.symm ▸ hF' l hc D _ _ _ _ a ha _ hc1, (fun i j=> (hF i j).2.1), H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,?_,grantR,archive,hσ⟩
  have hY:= hK₄ Y he3
  have hy (i j:ℕ): 0< ψ i j ∧ ψ i j≤ Time.credit G (s.profile j):=by obtain ⟨h,-,ht,-⟩:=(hζ i j).2; exact ⟨h,by linarith⟩
  let U' : Mallow.Trail F₀ τ:= ⟨N,N,fun i j h=> le_rfl,hp₀,fun i j h=> le_rfl,F'₀,m₀,ψ,hy,hK₂ Y he1,hK₃ Y he2,fun i j=>(hF j i).2.2.2.1 ⟩
  refine ⟨F₀,U',⟨μ,M',hY.spark,hY.receipts,hY.canopy⟩,⟨?_,hY.light,archive.top⟩,hM₂ _ he6,hM₀ _ he4,Zt,hM₁ _ he5,hX₇' _ he7,H₈' _ he8⟩
  intro m; let B':=A.B; let i:=B'.a.clock.J m; let j:= B'.a.clock.J (m+1)
  have hp:B'.a.params m=s.profile i:= params_eq B'.valid m
  exact hY.dawn j i (Push.PriceCompiler.step_paid B'.a m) (B'.a.clock.hatBeta m) (B'.valid.pays m) B'.a m hp rfl (hh.suitable _ (Push.PriceCompiler.first_le B'.valid m)|>.direct) -- order
end
end YM.PhysicalNext.Repeat.Legato.Round2
