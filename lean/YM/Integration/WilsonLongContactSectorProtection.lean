import YM.Integration.WilsonLongContactSectorCash

/-! A presold single-mark forecast, after the block is licensed and before the physical
cutoff or period. Its record remains the one used to issue Cash and Plays. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactSectorProtection
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open scoped Topology BigOperators Classical


variable {G : Gauge} {V : Type} (J : Request V) {P : Teller G}

/-- The protected property may use the purchased word order, its genuine target and its
original Heir record. The period and the physical radiator have not yet been selected. -/
abbrev Premium (G : Gauge) (n : ℕ) :=
  ∀ {P : Teller G}, ConnectedActivityE6.Target G P → Patch → Libretto G n → Booking G → ℝ → Prop

def Admitted (ρ : Premium G J.outputFieldOrder) : Prop :=
  ∀ {P : Teller G} (Q : ConnectedActivityE6.Target G P) (D : Patch) (C : Libretto G J.outputFieldOrder)
    (b : Booking G), D.Branches P.bind G → b.record.ε≤1/4 → ∀ᶠ x : ℝ in atTop, ρ Q D C b x

structure Offered (ρ : Premium G J.outputFieldOrder) (Δ : Daisy.Charity.RG12.Decal G)
    (Q : ConnectedActivityE6.Target G P) (C : Libretto G J.outputFieldOrder) (b : Booking G)
    (D : Patch) (x γ : ℝ) : Prop where
  window : Window J Δ Q C b D x γ
  small : b.record.ε ≤ 1/4
  forecast : ρ (target J Q) D C b x

theorem sale (ρ : Premium G J.outputFieldOrder) (grant : Admitted J ρ) (hG : G.Simple) (Δ : Daisy.Charity.RG12.Decal G) (Q : ConnectedActivityE6.Target G P) (H : Patch)
    (C : Libretto G J.outputFieldOrder) (branch : H.Branches P.bind G)
    (license : licensed C.δ C.N H.L) (cost : floor J Q Δ≤H.L.val)
    (stage : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), (teller J P).Funds S T →
      ∀ F, Matins T F J.inputDistanceOrder (2*C.C) C.M)
    (γ : ℝ) (hγ : -(1/2:ℝ)<γ) :
    ∃ b : Booking G, ∀ᶠ x : ℝ in atTop, Offered J ρ Δ Q C b H x γ := by
  obtain ⟨D,hd,_,hready⟩ := songs J P H C branch license stage (show 0<(1/4:ℝ) by norm_num)
  have supply := Target.quotesTogether (target J Q) (expense J Q)
  obtain ⟨W,hW,μ,α,o,hμ,_,hs⟩ := (supply.choose_spec H.L
    ((le_max_left _ _).trans ((le_max_left _ _).trans cost))).exists
  have press := Height.sailing (target J Q)
  have hc := press.choose_spec H.L ((le_max_right _ _).trans ((le_max_left _ _).trans cost)) (expense J Q) W μ α o hW hμ
    J.outputFieldOrder J.outputDistanceOrder Chi.canonical
  have hg := QLocalInheritedGlyphPurchase.charts hG (target J Q) o D C (QLocalRequestedHeirQuote.toll J)
    (QLocalInheritedSourcePrice.fee J C 505) 505 J.outputDistanceOrder Chi.canonical H.L γ hγ hd
    ((by decide : 2≤6).trans J.field_minimum) (show 0≤QLocalRequestedHeirQuote.toll J by dsimp [QLocalRequestedHeirQuote.toll]; linarith [J.output_support_pos])
  refine ⟨⟨D,W,μ,α,o⟩,?_⟩
  have ho := outer J Q ⟨D,W,μ,α,o⟩ H.L hμ
  have hk := hard_after J Q ⟨D,W,μ,α,o⟩ H.L hμ
  have hΔ := (Δ.good (teller J P) (target J Q) (expense J Q)).choose_spec H.L ((le_max_right _ _).trans cost)
    W μ o (teller J P).below H.J (by norm_num [expense]) hW hμ
  have protect := grant (target J Q) H C ⟨D,W,μ,α,o⟩ branch hd
  filter_upwards [hready,hs,hc,ho,hk,hΔ,hg,protect] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ hp
  exact ⟨⟨h₁,h₂,h₃,h₄ h₃,h₅,h₆,h₇⟩,hd,hp⟩

variable (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)

def Paid (ρ : Premium G J.outputFieldOrder) : Prediction G := fun {M} {D} {A} H =>
  ∃ b : ℕ → ℕ → Booking G,
    (∀ j i, StepStages j i → Earlier J M.p M.K extra j i (D.L j).val) ∧
    ∀ j x, A.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
      Offered J ρ Δ (H.target j i) (libretto J M.p M.K j i) (b j i)
        (Clockwork.patch D st fr) x γ ∧ Thermal G (D.L j) j (extra (M.p.profile i) i) x

theorem prepaid (ρ : Premium G J.outputFieldOrder) (grant : Admitted J ρ) (hG : G.Simple) (hγ : -(1/2:ℝ)<γ) (s : Sheet G) (K : MapPrices) :
    Prepaid (Paid J Δ extra γ ρ) s K := by
  intro Q E c C₀ z₂ b hW
  obtain ⟨u,_,_,h⟩ := collect_upper s.floorL
    (fun j L => ∀ i, StepStages j i → Earlier J s K extra j i L ∧ floor J (Q j i) Δ≤L)
    (fun j => eventually_transitions j _ _ (fun i _ =>
      (earlier J s K extra j i).and (eventually_ge_atTop (floor J (Q j i) Δ))))
  refine ⟨u,fun l hl D _ _ _ _ _ _ _ _ V' _ => ?_⟩
  have gate (j i) (st : StepStages j i) := h j (D.L j).val ((hl j).trans (D.large j).need) i st
  have rows (j i : ℕ) : ∃ b : Booking G, ∀ᶠ x : ℝ in atTop,
      ∀ (st : StepStages j i) (fr : s.first ≤ i),
        Offered J ρ Δ (Q j i) (libretto J s K j i) b (Clockwork.patch D st fr) x γ ∧
          Thermal G (D.L j) j (extra (s.profile i) i) x := by
    by_cases h : (StepStages j i ∧ (s.first ≤ i))
    · obtain ⟨b,hb⟩ := sale J ρ grant hG Δ (Q j i) (Clockwork.patch D h.1 h.2)
        (libretto J s K j i) (s.has _) (gate j i h.1).1.seam (gate j i h.1).2
        (calibrated J s K j i).2.2 γ hγ
      exact ⟨b,(hb.and (thermal_after G (D.L j) j (extra (s.profile i) i))).mono fun _ hx _ _ => hx⟩
    exact ⟨vacant G,Eventually.of_forall fun _ st fr => (h ⟨st,fr⟩).elim⟩
  choose b hb using rows
  obtain ⟨β,_,hv,hβ⟩ := collect_upper V'.betaEntry _
    (fun j => eventually_transitions j _ _ (fun i _=>hb j i))
  refine ⟨{V' with betaEntry:=β},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW K' I' hp B' B η q E' X J' K'' b' hZ hY hm
  exact ⟨b,fun j i st => Earlier.raised J s K (gate j i st).1 l,
    fun j x hx i st fr => hβ j x ((hW.beta j).trans hx) i st st fr⟩

/-- In particular the small recorded radius itself is always purchased. -/
def recordOnly : Premium G J.outputFieldOrder := fun _ _ _ _ _ => True

theorem small (hG : G.Simple) (hγ : -(1/2:ℝ)<γ) (s : Sheet G) (K : MapPrices) :
    Prepaid (Paid J Δ extra γ (recordOnly (G:=G) J)) s K := by
  apply prepaid J Δ extra γ _ _ hG hγ s K
  intro _ _ _ _ _ _ _
  exact Eventually.of_forall fun _ => trivial

end YM.Integration.WilsonLongContactSectorProtection
