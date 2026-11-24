import YM.FullVolume.Roll.Fiscal

/-! The free catalog, its directional cutoff, and the full-volume company
are chosen together. We retain the catalog when the original Fiscal proof
selects its sheet. This permits independent frame purchases before length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLengthsCatalog
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

open PhysicalNext.ThroughLaunch
variable {s : Sheet G} {T : MapPrices} {n : ℕ → ℕ} {L : Rolls (raise s n)} {Θ : Protection L} {D : Delays Θ}
    {Q : PostCost L} {Y : Bar D} {W : Wait Y}

open Next.Scheduling Next.SectorChange

-- PAY even if scheduling grows after this. These requirements available
-- on the j-height, not taken from a finally-chosen realization.
private lemma carryGates {E : Delays Θ} (h : Boost D E) (B : Extra.Multi.Scope) (t : Extra.Multi.Tariff)
    (Y : Extra.Multi.Gated D B t (localSection G)) : Extra.Multi.Gated E B t (localSection G) :=
  ⟨h.priced Y.priced,fun i j x hp hv hx => Y.gates i j x hp hv ((h.beta j).trans hx)⟩
private lemma carryCosmos {E : Delays Θ} (h : Boost D E) {Q : MapPrices} {g a X : ℕ → ℕ → ℝ}
    (Y : Cosmos (chart G) Q D g a X) : Cosmos (chart G) Q E g a X := by
  intro i j hj hv; obtain ⟨ha,hx,H⟩ := Y i j hj hv
  exact ⟨ha,hx,fun x he=> H x ((h.beta i).trans he)⟩

theorem purchase {K : KernelChoices} (hG : G.Simple) (hK : ∀ P : Patch, P.Branches K G) {o : Orders} (hp : Draft o)
    (C : ℕ → ℝ) (hC : ∀ i, 1≤C i) : ∃ (s : Sheet G) (O T : MapPrices) (l γ : ℕ → ℝ) (p : Bid.Worth),
    (∃ x b, Next.Free.Catalog K O l x b ∧ ∀ i, (s.profile i).clip.direct ≤ x i) ∧
    s.kernel = K ∧ WithStage s o ∧ ∀ (t : Tariffs) (B : Extra.Multi.Scope), ∃ v : ℕ → ℕ, Perceived s O T l γ C p t B v := by
  obtain ⟨O,l,g,b,h⟩:= Next.Free.reapsY K
  have catalog : Next.Free.Catalog K O l g b := by
    refine ⟨h.net, h.fit, ?_, h.hop⟩
    intro j hj c hc R
    obtain ⟨M, defined, covered, floors, sworn, _, top⟩ := h.bottom j hj c hc R
    exact ⟨M, defined, covered, floors, sworn, top⟩
  obtain ⟨σ,A,he,hA,hP⟩ := Stationary.verdant G hG O K g (fun i => (h.fit i).le) (Stationary.pouring G hG)
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
  refine ⟨s,O,T,l,γ,p,⟨g,b,catalog,fun i=>hB.axis i⟩,hs,hS,fun t B => ?_⟩
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
    Bid.recheck hx.beta hF, carryCosmos (s:=s) (n:=n) hx hE, fun X W A hA => ?_⟩
  have he1:A.clock.kernel=_ := (show A.clock.kernel=s.kernel from hA.kernel).trans hs -- def reduce
  have hT₀:= hA.stage
  have hi : Next.Free.Credit A g b := Next.Free.credit_from_sheet hA g b (fun i _=> hB.axis i)
    (fun i _=> le_trans (show b i ≤ s.floorL i from (congr_fun ((hu).trans hX') i) ▸ hw i) ((hv.trans hV) i))
  obtain ⟨M,hM⟩:= Next.Free.wardrobe A O l g b (he1.symm ▸ h) hi
  obtain ⟨H,h₅,h₆,hs₀⟩:= hY₀ A hT₀ (he1.trans hs.symm) M hM h.net
  obtain ⟨h₇,h₈⟩:= Next.Free.retained_presents _ _ _ _ hM.offered hM.classic h₅
  have h₃:=hM.classic; have h₄:= hM.offered
  have hK : Δ ≤ S.betaEntry := fun i => le_trans (le_max_right ..) ((le_max_right ..).trans (hT.beta i))
  obtain ⟨X',hΨ₀,U,hΞ⟩ := hH S X W hK ((show x ≤ W'.shells from fun _=>le_max_left ..).trans hT.shells) Q h1 h2 h3 A hA M H h₃ h₅
    (chart G) (chart_ok G)
  have hU:=hΞ.sight
  have hcΞ:=Stationary.Artes.yields (show Stationary.Artes.Counter A H (O:=chart G) Q X' T from ⟨hΨ₀,h₆,fun i j hx k=> h₈ _ _ _ hx, chart_ok G,Stationary.colorAvail G hG⟩) hΞ hs₀
  obtain ⟨J,j,H',Hj,hp,hp',ha,ha',hz₀,haX⟩ := changeP s T hQ hA h₆ (chart_ok G) U hU.linked
  have hΓ (i) : j.path i i=Design.top G (A.params i).clip := hp ▸ if_pos rfl
  refine ⟨ht n (hu'.trans hn) L A hA.lengths hA.stage (fun m => ?_), Extra.Multi.Gated.prepares S _ _ _ hN
    (fun j=> le_trans (le_trans (le_max_right ..) (hn j)) (L.large j).need) (carryGates (s:=s) (n:=n) (hDE.chain hx) B K ‹Extra.Multi.Gated Q' B K (localSection G)›) hA,
    J,j,⟨H',Hj,hΓ, M,H,U, h₃,h₄,h₅,h₆,h₇,h₈,hU,hp,hp',ha,ha',haX⟩,Stationary.Artes.replayQ hcΞ ?_ ?_ ?_,Stationary.Artes.history_copy hs₀ ?_ ?_⟩
  swap
  all_goals first
  | (intro i; exact (eventually_gt_atTop i).mono fun n hx=> by dsimp only; rw [hp,Change.revised, if_neg hx.ne])
  | (intro i; rw [hp'])
  | (intro i y F; exact (eventually_gt_atTop (i+1)).mono fun n hx=> (ha _ _ _ _ hx).symm)
  | (intro i; exact (eventually_gt_atTop i).mono fun n hx=>(ha'.other _ _ hx).symm) -- fix '..'
  | (intro i; exact (eventually_gt_atTop (i+1)).mono fun n hx=> (hz₀ _ _ hx).symm)
  | exact (le_trans (le_max_left ..) ((le_max_right ..).trans (hT.beta _))).trans (hA.pays _)
end YM.Integration.WilsonMatrixTicketLengthsCatalog
