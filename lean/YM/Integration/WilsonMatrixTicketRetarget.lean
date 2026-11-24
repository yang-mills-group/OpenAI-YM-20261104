import YM.FullVolume.Roll.Fiscal

/-! The recovered OPE consumer's shop on the actual retained map quote.
The supplier below uses the very same post-cost, horizon and stationary path. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketRetarget
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open PhysicalNext PhysicalNext.ThroughLaunch Next.Scheduling Next.SectorChange
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}

structure View (s : Sheet G) (O T : MapPrices) (l γ C : ℕ → ℝ) (p : Bid.Worth)
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
              Extra.Multi.Prepared B K (localSection G) a ∧ ∃ (M : Horizon a) (k : Kin M (chart G)), Imperial O T l Q a M k

theorem of_perceived {s:Sheet G} {O T:MapPrices} {l γ C:ℕ→ℝ} {p:Bid.Worth}
    {t:Tariffs} {B:Extra.Multi.Scope} {v:ℕ→ℕ} (h:Perceived s O T l γ C p t B v):
    View s O T l γ C p t B v:=by
  refine ⟨h.slopePrice,h.suitable,h.liftL,h.plan,?_⟩
  intro n hn L
  obtain ⟨η,gap,post⟩:=h.ship n hn L
  refine ⟨η,gap,?_⟩
  intro Q hQ hΓ hγ Θ K z hz A
  obtain ⟨D,hD,F,κ,ℓ,hF,late⟩:=post Q hQ hΓ hγ Θ K z hz A
  refine ⟨D,hD,F,κ,ℓ,hF,?_⟩
  intro E hE
  obtain ⟨prices,stock,ringing,cosmos,actual⟩:=late E hE
  refine ⟨prices,stock,ringing,cosmos,?_⟩
  intro Y W a ha
  obtain ⟨doors,prep,M,k,imperial,_cadre,_amplify⟩:=actual Y W a ha
  exact ⟨doors,prep,M,k,imperial⟩

end YM.Integration.WilsonMatrixTicketRetarget
