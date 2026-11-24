import YM.QuadraticLocal.Found.Mastery
import YM.Integration.WilsonFundedWindowCompany
import YM.Integration.WilsonWindowRootPurchase

/-! Prepayment for the historical marked books on the chosen physical sheet.
The cost of a law is expressed at the actual price used to select its roots.
The tab, books and register then persist through every subsequent delay. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonWindowBookPurchase

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source JointLoad JointLoad.Heir JointLoad.Heir.Suite
open JointLoad.Psalm Clockwork AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Geo ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Time
open Next.Foundations UVNext.CouplingReset Cub Circlet Graces Roost Pressure
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonFundedWindowCompany
open scoped Topology BigOperators Classical

variable {G : Gauge} {φ : ℕ → ℕ}

abbrev raised (s : Sheet G) (price : MapPrices) (l : ℕ → ℕ) : Metals G :=
  ⟨ThroughLaunch.raise s l, price, chart G, chart_ok G⟩

/-- An invoice for an existing law at the indicated price.  No identity
between two independently selected prices is part of this condition. -/
def Permitted (law : VowsR.LawScroll G φ) (s : Sheet G) (price : MapPrices) : Prop :=
  ∀ (R : Roots (G := G) s.profile price s.kernel) (C : Targets s price) (E : Expenses C),
    (∀ j i, (C j i).table = chart G ∧ (C j i).halo = 500 ∧
      (E j i).earn = rays s j i ∧ (E j i).wanting = -(7/16:ℝ) ∧ (E j i).degrees = 0) →
    ∃ l₀ : ℕ → ℕ, ∀ l : ℕ → ℕ, l₀ ≤ l → ∀ (D : Rolls (ThroughLaunch.raise s l))
      (w : Return.Wages) (u : ℕ → ℝ) (Z : Repeat.Register D E w u)
      (post : ℕ → ℕ → Postage) (scouts : Time.Scouts (F := post)),
      Pocket Z scouts → ∀ (P : PostCost D) (θ : Protection D)
        (tab : Roots.Tab (X := raised s price l) R D)
        (B : Offices.Books (X := raised s price l) R D tab φ),
        Offices.Sales (X := raised s price l) R D tab Z scouts φ B →
        ∀ V : Delays θ, ∃ W : Delays θ, DelayLe V W ∧
          ∀ W', DelayLe W W' →
            law.clause (raised s price l) D P C E u w Z post scouts R tab B θ W'

/-- The eight book and delay fields of the original chamber, attached to the
one tab actually selected for the original rolls. -/
def Held (hG : G.Simple) (law : VowsR.LawScroll G φ) : Prediction G :=
  fun {M} {D} {A} F =>
    let R := roots hG M.p M.K
    let tab := rollTab hG M D
    ∃ B : Offices.Books R D tab φ,
      Beaming.Frost F.shape F.book F.scout A.delay ∧ Spes.Market.Warm A.delay ∧
      (∀ j, Poetry.Agenda.Crews R φ j (D.L j).val) ∧ Institute F.target M.p.floorL ∧
      Pocket F.shape F.scout ∧ Offices.Sales R D tab F.shape F.scout φ B ∧
      Educated R D tab F.shape F.scout φ B A.delay ∧
      law.clause M D A.post F.target F.expense F.duration F.walls F.shape F.book F.scout
        R tab B A.θ A.delay

theorem prepaid (hG : G.Simple) (law : VowsR.LawScroll G φ) (s : Sheet G) (price : MapPrices)
    (invoice : Permitted law s price) : Prepaid (@Guard G (@Held G φ hG law)) s price := by
  classical
  intro C E hchart programs wage baton wanting
  by_cases flags : ∀ j i, (C j i).table = chart G ∧ (C j i).halo = 500 ∧
      (E j i).earn = rays s j i ∧ (E j i).wanting = -(7/16:ℝ) ∧ (E j i).degrees = 0
  · let R := roots hG s price
    have rate (j i : ℕ) (_ : StepStages j i) : 3/8 + (C j i).rate < 0 := by
      have h := (E j i).reach
      rw [wanting j i] at h
      linarith
    have extent (j i : ℕ) (_ : StepStages j i) :
        (s.profile i).supportExponent + 1 + 1 < (C j i).exp := by
      have h := (E j i).worth
      rw [(flags j i).2.2.1] at h
      unfold rays at h
      linarith [(E j i).first, (E j i).second]
    obtain ⟨f, freq⟩ := Beaming.orbit C rate extent
    obtain ⟨g, lease⟩ := Mentor.leases C rate extent
    obtain ⟨c, crews⟩ := Poetry.Agenda.widen R φ
    obtain ⟨a, approve⟩ := invoice R C E flags
    refine ⟨f ⊔ (g ⊔ (c ⊔ a)), ?_⟩
    intro l hl D w u Z post scouts θ stages P V quarter
    obtain ⟨hf, hrest⟩ := sup_le_iff.mp hl
    obtain ⟨hg, hrest⟩ := sup_le_iff.mp hrest
    obtain ⟨hc, ha⟩ := sup_le_iff.mp hrest
    by_cases oriented : Pocket Z scouts
    · let M := raised s price l
      let tab := rollTab hG M D
      have booked (x : ℕ) : Poetry.Agenda.Crews R φ x (D.L x).val :=
        crews _ _ ((hc x).trans (D.large x).need)
      have leased : Institute (S := M.p) C M.p.floorL := by
        intro i j step L he
        exact lease i j step L ((hg i).trans he)
      obtain ⟨B, sales⟩ := Offices.formation (X := M) R D tab Z scouts φ booked
        hchart oriented (fun x => (D.large x).need) leased
      obtain ⟨V₁, h₁, frost⟩ := Beaming.option Z post scouts oriented
        (show Beaming.Freq (P' := M.p) C f from freq)
        (fun x => (hf x).trans (D.large x).need) V
      obtain ⟨V₂, h₂, warm⟩ := Spes.Market.accrue V₁
      obtain ⟨V₃, h₃, teach⟩ := Mentor.educates (X := M) R D tab Z scouts φ B sales V₂
      obtain ⟨V₄, h₄, signed⟩ := approve l ha D w u Z post scouts oriented P θ tab B sales V₃
      refine ⟨V₄, h₁.trans (h₂.trans (h₃.trans h₄)), ?_⟩
      intro W hW bar wait priced directed
      dsimp only
      intro η q exchange menu aux quote booth sheltered works divides guard
      exact ⟨B, frost W (h₂.trans (h₃.trans (h₄.trans hW))),
        warm W (h₃.trans (h₄.trans hW)), booked, leased, oriented, sales,
        teach W (h₄.trans hW), signed W hW⟩
    · refine ⟨V, DelayLe.refl V, ?_⟩
      intro W hW bar wait priced directed
      dsimp only
      intro η q exchange menu aux quote booth sheltered works divides guard
      exact (oriented guard.2).elim
  · refine ⟨0, ?_⟩
    intro l hl D w u Z post scouts θ stages P V quarter
    refine ⟨V, DelayLe.refl V, ?_⟩
    intro W hW bar wait priced directed
    dsimp only
    intro η q exchange menu aux quote booth sheltered works divides guard
    exact (flags guard.1).elim

theorem chamber (hG : G.Simple) (law : VowsR.LawScroll G φ)
    {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (F : Roost.Factor A)
    (h : Held hG law F)
    (ticket : TicketP A F (roots hG M.p M.K) (rollTab hG M D)) :
    ∃ B, VowsR.Chamber law F (roots hG M.p M.K) (rollTab hG M D) B := by
  obtain ⟨B, hf, hw, hc, hl, ho, hs, he, hβ⟩ := h
  exact ⟨B, ticket, hf, hw, hc, hl, ho, hs, he, hβ⟩

end YM.Integration.WilsonWindowBookPurchase
end

