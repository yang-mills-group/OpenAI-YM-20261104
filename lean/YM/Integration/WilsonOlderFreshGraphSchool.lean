import YM.Integration.WilsonOlderFreshGraphStrip
import YM.Integration.WilsonWindowJointPurchase

/-! Before L, retain the same narrow roots, rolls and books for all marked enrollments on the original Wilson factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSchool

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source JointLoad JointLoad.Heir JointLoad.Heir.Suite
open JointLoad.Psalm Clockwork AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Geo ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Time
open Next.Foundations UVNext.CouplingReset Cub Circlet Graces Roost Pressure
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowCompany
open AllOrder AllOrder.Floe
open scoped Topology BigOperators Classical


structure Menu where
  width : (ℕ→Stage) → MapPrices → KernelChoices → ℕ→ℕ→ℝ
  positive : ∀A p K k x,0<width A p K k x
  shell : ℕ→ℝ
  cost : ∀ k,0<shell k

def roots {G:Gauge} (menu:Menu) (hG:G.Simple) (s:Sheet G) (p:MapPrices) : Roots (G:=G) s.profile p s.kernel :=
  WilsonOlderFreshGraphStrip.roots hG s.profile p s.kernel (menu.width s.profile p s.kernel) menu.shell
    (menu.positive s.profile p s.kernel) menu.cost

def rollTab {G:Gauge} (menu:Menu) (hG:G.Simple) (M:Metals G) (D:Rolls M.p) : Roots.Tab (X:=M) (roots menu hG M.p M.K) D :=
  Classical.choice (Roots.options (X:=M) D (roots menu hG M.p M.K) hG)

variable {G:Gauge} {φ:ℕ→ℕ}
def Issued (menu:Menu) (hG : G.Simple) : Prediction G := fun {M} {D} {A} F =>
  TicketP A F (roots menu hG M.p M.K) (rollTab menu hG M D)

theorem ticket (menu:Menu) (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Issued G menu hG) s price := by
  intro C E flags programs wages baton
  let R := roots menu hG s price
  obtain ⟨a, rise⟩ := R.prize
  obtain ⟨b, lodge⟩ := AllOrder.Shop.leased s C E
  obtain ⟨c, needed⟩ := AllOrder.Transit.must s price E wages
  refine ⟨a ⊔ (b ⊔ c), ?_⟩
  intro l hl D w u Z post scouts pocket θ stages P payments V quarter
  obtain ⟨ha, hrest⟩ := sup_le_iff.mp hl
  obtain ⟨hb, hc⟩ := sup_le_iff.mp hrest
  let M : Metals G := ⟨ThroughLaunch.raise s l, price, chart G, chart_ok G⟩
  let tab := rollTab menu hG M D
  have high (x : ℕ) : R.Rise x ((D.L x).val : ℝ) :=
    rise x (D.L x) ((ha x).trans (D.large x).need)
  have required : AllOrder.Transit.Needed M.p M.K E wages l := by
    exact ⟨fun i j L step hL => needed.hair i j L step ((hc j).trans hL),
      fun j i step L hL => needed.acts j i step L ((hc j).trans hL)⟩
  obtain ⟨V₁, h₁, stay⟩ := AllOrder.Shop.funding (X := M) D Z
    (fun _ i => AllOrder.Shop.edgeW i) V (show AllOrder.Shop.Freq (s := M.p) E b from lodge)
    (fun j => (hb j).trans (D.large j).need)
    (fun j i _ => (E j i).reach.trans (by rw [(flags j i).2.2.2.1]; norm_num))
    (fun _ i => AllOrder.Shop.edge_pp i)
  obtain ⟨V₂, h₂, tour⟩ := AllOrder.Transit.predicts (X := M) Z R tab wages programs (rays s)
    mile stages scouts (wind payments) hG required (fun i j _ => (flags i j).1)
    (fun i j _ => (flags i j).2.2.2.1)
    (fun i j _ => by unfold rays; linarith [(s.profile j).price_pos]) quarter V₁
  obtain ⟨V₃, h₃, receipts⟩ := Roots.summit (X := M) D R high tab V₂
  obtain ⟨V₄, h₄, header⟩ := demands (X := M) V₃
  refine ⟨V₄, h₁.trans (h₂.trans (h₃.trans h₄)), ?_⟩
  intro W hW bar wait priced directed archive origins shape
  dsimp only
  intro η q exchange aux quote booth sheltered works divides
  exact ⟨⟨tour W (h₃.trans (h₄.trans hW)),
    ⟨high, receipts W (h₄.trans hW), stay W (h₂.trans (h₃.trans (h₄.trans hW))),
      archive, shape⟩⟩, header W hW⟩

def Held (menu:Menu) (hG : G.Simple) (law : VowsR.LawScroll G φ) : Prediction G :=
  fun {M} {D} {A} F =>
    let R := roots menu hG M.p M.K
    let tab := rollTab menu hG M D
    ∃ B : Offices.Books R D tab φ,
      Beaming.Frost F.shape F.book F.scout A.delay ∧ Spes.Market.Warm A.delay ∧
      (∀ j, Poetry.Agenda.Crews R φ j (D.L j).val) ∧ Institute F.target M.p.floorL ∧
      Pocket F.shape F.scout ∧ Offices.Sales R D tab F.shape F.scout φ B ∧
      Educated R D tab F.shape F.scout φ B A.delay ∧
      law.clause M D A.post F.target F.expense F.duration F.walls F.shape F.book F.scout
        R tab B A.θ A.delay

theorem prepaid (menu:Menu) (hG : G.Simple) (law : VowsR.LawScroll G φ) (s : Sheet G) (price : MapPrices)
    (invoice : WilsonWindowBookPurchase.Permitted law s price) : Prepaid (@Guard G (@Held G φ menu hG law)) s price := by
  classical
  intro C E hchart programs wage baton wanting
  by_cases flags : ∀ j i, (C j i).table = chart G ∧ (C j i).halo = 500 ∧
      (E j i).earn = rays s j i ∧ (E j i).wanting = -(7/16:ℝ) ∧ (E j i).degrees = 0
  · let R := roots menu hG s price
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
    · let M := WilsonWindowBookPurchase.raised s price l
      let tab := rollTab menu hG M D
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

theorem chamber (menu:Menu) (hG : G.Simple) (law : VowsR.LawScroll G φ)
    {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (F : Roost.Factor A)
    (h : Held menu hG law F)
    (ticket : TicketP A F (roots menu hG M.p M.K) (rollTab menu hG M D)) :
    ∃ B, VowsR.Chamber law F (roots menu hG M.p M.K) (rollTab menu hG M D) B := by
  obtain ⟨B, hf, hw, hc, hl, ho, hs, he, hβ⟩ := h
  exact ⟨B, ticket, hf, hw, hc, hl, ho, hs, he, hβ⟩


open WilsonFundedWindowMenu WilsonWindowJointPurchase
def grant (menu:Menu) (hG:G.Simple) (law:VowsR.LawScroll G φ) : Prediction G :=
  Together (@Held G φ menu hG law) (@Issued G menu hG)

theorem before_period (menu:Menu) (hG:G.Simple) (law:VowsR.LawScroll G φ)
    (bought : ∀(s:Sheet G)(q:MapPrices),WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s q)) :
    AllPrices (@grant G φ menu hG law) := fun s q=>
  joint (from_guard (prepaid menu hG law s _ (bought s q))) (ticket menu hG s _)

theorem on_run (menu:Menu) (hG:G.Simple) (law:VowsR.LawScroll G φ) (R:Run G) (purchase:grant menu hG law R.kit) :
    (∃ B,VowsR.Chamber law R.kit (roots menu hG R.metals.p R.metals.K) (rollTab menu hG R.metals R.rolls) B) ∧
    ∀k x,1≤k→Poetry.Agenda.seed (roots menu hG R.metals.p R.metals.K) φ k x≤
      menu.width R.metals.p.profile R.metals.K R.metals.p.kernel k x/(16*menu.shell k) := by
  exact ⟨chamber menu hG law R.kit purchase.1 purchase.2,fun k x hk=>WilsonOlderFreshGraphStrip.narrow
    hG _ _ _ _ _ _ _ φ k x hk⟩

end YM.Integration.WilsonOlderFreshGraphSchool
end
