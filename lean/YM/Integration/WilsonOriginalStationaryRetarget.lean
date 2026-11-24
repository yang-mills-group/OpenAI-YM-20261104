import YM.Integration.WilsonOriginalStationaryLightPurchase
import YM.FullVolume.Roll.Fiscal

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.ThroughLaunch
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

open Next.Scheduling Next.SectorChange
open private carC carG from YM.FullVolume.Roll.Fiscal
structure PerceivedWithLight (cap : ℝ → ℝ) (s : Sheet G) (O T : MapPrices) (l γ C : ℕ → ℝ) (p : Bid.Worth)
    (t : Tariffs) (B : Extra.Multi.Scope) (v : ℕ → ℕ) : Prop where
  slopePrice i : 0<γ i
  suitable i : s.first ≤ i → Design.Suitable G (s.profile i)
  liftL : s.floorL ≤ v
  plan : Doors.Plans s C p
  -- θ thresholds imposed later; shell growth can still be enlarged there
  ship (n : ℕ→ℕ) (hn : v ≤ n) (L : Rolls (raise s n)) :
    ∃ η : ℕ→ℝ, Stationary.BudgetGap (raise s n) L O η ∧
    ∀ Q : PostCost L, Q.η=η → 1 ≤ Q.Γ → Q.c ≤ γ →
    ∀ (Θ : Protection L) (K : Extra.Multi.Tariff) (z : ℝ), 0 ≤ z → ∀ A : Delays Θ,
      ∃ D : Delays Θ, Boost A D ∧
        ∃ F κ ℓ : ℕ → ℕ → ℝ,(∀ i j, z ≤ F i j) ∧ ∀ E : Delays Θ, Boost D E →
          Prices (raise s n) t (localSection G) E.betaEntry ∧ Stock.Priced E ∧
          Ringing (raging s T) F E ∧ Cosmos (chart G) (raging s T) E F κ ℓ ∧
            ∀ (Y : Bar E) (W : Wait Y) (a : Levels G), Paid W a → Doors.Budget a C p ∧
              Extra.Multi.Prepared B K (localSection G) a ∧ ∃ (M : Horizon a) (k : Kin M (chart G)), Imperial O T l Q a M k ∧ Stationary.Artes.Cadre Q k ∧ Next.Free.Amplify M ∧ Stationary.LightPath k cap

theorem PerceivedWithLight.ordinary {cap : ℝ → ℝ} {s : Sheet G} {O T : MapPrices}
    {l γ C : ℕ → ℝ} {p : Bid.Worth} {t : Tariffs} {B : Extra.Multi.Scope} {v : ℕ → ℕ}
    (h : PerceivedWithLight cap s O T l γ C p t B v) : Perceived s O T l γ C p t B v := by
  refine ⟨h.slopePrice, h.suitable, h.liftL, h.plan, ?_⟩
  intro n hn L
  obtain ⟨η, budget, ship⟩ := h.ship n hn L
  refine ⟨η, budget, ?_⟩
  intro Q hη hΓ hc θ tariff x hx V
  obtain ⟨D, boost, F, κ, ℓ, floor, pay⟩ := ship Q hη hΓ hc θ tariff x hx V
  refine ⟨D, boost, F, κ, ℓ, floor, ?_⟩
  intro E he
  obtain ⟨price, stock, ring, routes, settle⟩ := pay E he
  refine ⟨price, stock, ring, routes, ?_⟩
  intro bar wait levels paid
  obtain ⟨doors, ready, M, j, imperial, cadre, amplified, _⟩ := settle bar wait levels paid
  exact ⟨doors, ready, M, j, imperial, cadre, amplified⟩

theorem sailsWithLight (cap : ℝ → ℝ) (movable : Stationary.Movable cap) {K : KernelChoices} (hG : G.Simple) (hK : ∀ P : Patch, P.Branches K G) {o : Orders} (hp : Draft o)
    (C : ℕ → ℝ) (hC : ∀ i, 1≤C i) : ∃ (s : Sheet G) (O T : MapPrices) (l γ : ℕ → ℝ) (p : Bid.Worth),
    s.kernel = K ∧ WithStage s o ∧ ∀ (t : Tariffs) (B : Extra.Multi.Scope), ∃ v : ℕ → ℕ, PerceivedWithLight cap s O T l γ C p t B v := by
  obtain ⟨O,l,g,b,h⟩:= Next.Free.reapsY K
  obtain ⟨σ,A,he,hA,hP⟩ := Stationary.verdantWithLight cap movable G hG O K g (fun i => (h.fit i).le) (Stationary.pouring G hG)
  obtain ⟨X,hX,hX',hx,hx'⟩ := housing hK hp b g σ h.fit he
  obtain ⟨a,c,hY⟩ := Further.StrongStartup.shelves X (fun i _ => (hx' i).2.1)
  let G' i := max (a i) (A i)
  obtain ⟨Y,hj,hY',hu,h1,h2⟩ := buy_shelves X G' c
  obtain ⟨hc,-⟩ := hY Y hj (fun i => let ⟨h1,h2,h3,h4,h5⟩ := h1 i; ⟨h1,h2,h3,(le_max_left ..).trans h4,h5⟩)
  have ho : WithStage Y o := ⟨hj.trans hx.first,fun i=>(h1 i).2.2.1.trans (hx.jets _), fun i=>(h2 i).1.trans (hx.powers _),
    fun i=>(h2 i).2.1.trans (hx.prices _)⟩
  let P i := (Y.profile i).width; let A' i := (Y.profile i).paths
  have hσ : P ≤ σ := fun i => ((h1 i).2.1.trans (hx' i).2.2).le
  have hs0 : A ≤ A' := fun i => (le_max_right ..).trans (h1 i).2.2.2.1
  obtain ⟨d,γ,u,-,hg,H⟩ := hP P A' hσ (fun i => (Y.profile i).width_pos) hs0
  have hY (i : ℕ) : (Y.profile i).clip.direct ≤ g i := by rw [(h1 i).1]; exact (hx' i).1
  obtain ⟨s,p,hs,hS,hc',hw,hB,hN,hQ⟩ := developer Y (hY'.trans hX) hc hY ho hp u d C hC
  obtain ⟨T,hY₀⟩:= Next.Free.relayT (P:=s) (X:=O) (l:=l)
  obtain ⟨u,e,ht⟩ := Doors.afford s C p hc'
  refine ⟨s,O,T,l,γ,p,hs,hS,fun t B => ?_⟩
  obtain ⟨v,r,hv,hr⟩ := Further.StrongStartup.prices s (raging s T) B t (localSection G) hG
    (fun i hi => (hQ i hi).direct) hN
  let v' j := max (max (v j) (u j)) (B.ask j (s.profile j))
  have hv' : v ≤ v' := fun _ => le_trans (le_max_left ..) (le_max_left ..)
  have hu' : u ≤ v' := fun _ => le_trans (le_max_right ..) (le_max_left ..)

  refine ⟨v',⟨hg,hQ,hv.trans hv',hc',fun n hn L => ?_⟩⟩
  have hV := hv'.trans hn
  obtain ⟨x,y,hy,hZ⟩ := H (raise s n) hs ⟨hB.axis,hB.fields,hB.gradient,
      fun i => (hB.days i).trans ((hv.trans hV) i)⟩ L
  obtain ⟨hb,hr⟩ := hr n hV
  refine ⟨y,hy,fun Q h1 h2 h3 Θ K z hz W => ?_⟩
  obtain ⟨Δ,hH⟩ := hZ Θ
  let W' : Delays Θ := {W with shells:=fun i=> max (x i) (W.shells i),
                                 betaEntry:=fun i=> max (W.betaEntry i) (max (e i) (Δ i))}
  obtain ⟨D,hv₀,hv₁,hp₀,hp₁,hp₂,F,hF,hF',hG'⟩ := hr L K z hz Θ W'
  obtain ⟨Q',hq',hq,h',hd,hU⟩ := Extra.Multi.raise_gates hG D B K (localSection G)
  have hdB : Boost D Q' := ⟨h',hd,hq'.symm.le,hq.symm.le⟩
  obtain ⟨E,hDE,hF,hΓ,hΩ,hE⟩ := issue_cosmos (chart G) (raging s T) (chart_ok G) Q' F (Bid.recheck hdB.beta hF)
  have hDE' := hdB.chain hDE
  have HW : Boost W' D := ⟨hp₁,hp₀,hv₀.symm.le,hv₁.symm.le⟩
  have hW : Boost W E := (Boost.chain (V:=W) (W:=W') ⟨fun _ => le_max_left ..,le_rfl,fun _ => le_max_right ..,le_rfl⟩ HW).chain hDE'
  refine ⟨E,hW,F,hΓ,hΩ,hF',fun S hx => ?_⟩
  have hz := hDE'.chain hx; have hT := HW.chain hz
  refine ⟨hb _ (le_trans hp₂ hz.beta), Boost.priced (hDE.chain hx) hU.priced,
    Bid.recheck hx.beta hF, carC (s:=s) (n:=n) hx hE, fun X W A hA => ?_⟩
  have he1:A.clock.kernel=_ := (show A.clock.kernel=s.kernel from hA.kernel).trans hs -- def reduce
  have hT₀:= hA.stage
  have hi : Next.Free.Credit A g b := Next.Free.credit_from_sheet hA g b (fun i _=> hB.axis i)
    (fun i _=> le_trans (show b i ≤ s.floorL i from (congr_fun ((hu).trans hX') i) ▸ hw i) ((hv.trans hV) i))
  obtain ⟨M,hM⟩:= Next.Free.wardrobe A O l g b (he1.symm ▸ h) hi
  obtain ⟨H,h₅,h₆,hs₀⟩:= hY₀ A hT₀ (he1.trans hs.symm) M hM h.net
  obtain ⟨h₇,h₈⟩:= Next.Free.retained_presents _ _ _ _ hM.offered hM.classic h₅
  have h₃:=hM.classic; have h₄:= hM.offered
  have hK : Δ ≤ S.betaEntry := fun i => le_trans (le_max_right ..) ((le_max_right ..).trans (hT.beta i))
  obtain ⟨X',hΨ₀,U,hΞ,sourceLight⟩ := hH S X W hK ((show x ≤ W'.shells from fun _=>le_max_left ..).trans hT.shells) Q h1 h2 h3 A hA M H h₃ h₅
    (chart G) (chart_ok G)
  have hU:=hΞ.sight
  have hcΞ:=Stationary.Artes.yields (show Stationary.Artes.Counter A H (O:=chart G) Q X' T from ⟨hΨ₀,h₆,fun i j hx k=> h₈ _ _ _ hx, chart_ok G,Stationary.colorAvail G hG⟩) hΞ hs₀
  obtain ⟨J,j,H',Hj,hp,hp',ha,ha',hz₀,haX⟩ := changeP s T hQ hA h₆ (chart_ok G) U hU.linked
  have hΓ (i) : j.path i i=Design.top G (A.params i).clip := hp ▸ if_pos rfl
  have retained : Stationary.LightPath j cap := by
    intro N i hi
    have bounds := Hj.cap N i hi
    by_cases he : i = N
    · subst N
      have unit := (sourceLight i i le_rfl).two
      have nonneg : 0 ≤ cap (A.clock.hatBeta i) := (tsum_nonneg unit.1).trans unit.2.2
      unfold Stationary.Light
      refine { bounds with two := ?_ }
      have zero (k : ℕ) : ((j.path i i).loop k).coeff = 0 := Hj.initial i k
      obtain ⟨legal, finite, _⟩ := bounds.two
      exact ⟨legal, finite, by simpa [RG.Atom.budget,RG.Atom.magnitude,zero] using nonneg⟩
    · change Stationary.Light cap A i _
      rw [hp, show Change.revised U N i = U.path N i from if_neg he]
      exact sourceLight N i hi
  refine ⟨ht n (hu'.trans hn) L A hA.lengths hA.stage (fun m => ?_), Extra.Multi.Gated.prepares S _ _ _ hN
    (fun j=> le_trans (le_trans (le_max_right ..) (hn j)) (L.large j).need) (carG (s:=s) (n:=n) (hDE.chain hx) B K ‹Extra.Multi.Gated Q' B K (localSection G)›) hA,
    J,j,⟨H',Hj,hΓ, M,H,U, h₃,h₄,h₅,h₆,h₇,h₈,hU,hp,hp',ha,ha',haX⟩,Stationary.Artes.replayQ hcΞ ?_ ?_ ?_,Stationary.Artes.history_copy hs₀ ?_ ?_,retained⟩
  swap
  all_goals first
  | (intro i; exact (eventually_gt_atTop i).mono fun n hx=> by dsimp only; rw [hp,Change.revised, if_neg hx.ne])
  | (intro i; rw [hp'])
  | (intro i y F; exact (eventually_gt_atTop (i+1)).mono fun n hx=> (ha _ _ _ _ hx).symm)
  | (intro i; exact (eventually_gt_atTop i).mono fun n hx=>(ha'.other _ _ hx).symm) -- fix '..'
  | (intro i; exact (eventually_gt_atTop (i+1)).mono fun n hx=> (hz₀ _ _ hx).symm)
  | exact (le_trans (le_max_left ..) ((le_max_right ..).trans (hT.beta _))).trans (hA.pays _)
end YM.PhysicalNext.ThroughLaunch
end
