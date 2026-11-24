import YM.AllOrder.Transit.Tavern
import YM.Integration.WilsonFundedWindowMenu
import YM.Integration.WilsonWindowRootPurchase

/-! Buy the physical ticket at the menu chosen before the delay. Its two
directed-field inputs are the archive and the shape of the referee's very
same field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonWindowTicketPurchase
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source JointLoad JointLoad.Heir JointLoad.Heir.Suite
open JointLoad.Psalm Clockwork AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Geo ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Time
open Next.Foundations UVNext.CouplingReset Cub Circlet Graces Roost Pressure
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonWindowRootPurchase
open scoped Classical

variable {G : Gauge}

def Issued (hG : G.Simple) : Prediction G := fun {M} {D} {A} F =>
  TicketP A F (roots hG M.p M.K) (rollTab hG M D)

theorem prepaid (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Issued G hG) s price := by
  intro C E flags programs wages baton
  let R := roots hG s price
  obtain ⟨a, rise⟩ := R.prize
  obtain ⟨b, lodge⟩ := AllOrder.Shop.leased s C E
  obtain ⟨c, needed⟩ := AllOrder.Transit.must s price E wages
  refine ⟨a ⊔ (b ⊔ c), ?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨ha, hrest⟩ := sup_le_iff.mp hl
  obtain ⟨hb, hc⟩ := sup_le_iff.mp hrest
  let M : Metals G := ⟨ThroughLaunch.raise s l, price, chart G, chart_ok G⟩
  let tab := rollTab hG M D
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
    mile stages scouts (wind menu) hG required (fun i j _ => (flags i j).1)
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

end YM.Integration.WilsonWindowTicketPurchase
end

