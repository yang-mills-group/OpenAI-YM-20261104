import YM.Integration.WilsonConditionalTaylorCalendar
import YM.Integration.WilsonWindowBookPurchase
import YM.Integration.FVA1Physical.Wilson.PacketInvoice

/-! Fund the original Wilson conditional packet, vacuum and thermal receipts
on the same physical rolls, register, prices, and wait. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorPurchase

open Function Filter Set Finset Lattice RG RG.Shoot YM.Wilson Precision RG.Supply Input Org
open Extra.Histories Source PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open FVA1Physical.Wilson WilsonLimitConstruction.FundedCompanySelection
open scoped Topology BigOperators Classical

variable {G : Gauge}

def Inventory (u : G.ColorIndex) (V : MSbar.Heath.Voice G) : Prediction G := fun {M} {D} {A} F =>
  M.O=chart G ∧ packetInvoice u V M D A F ∧ vacuumInvoice u V M D A F

/-- The vacuum and mixed packet offers are issued against the exact map price of
the original selector and joined before the physical wait is chosen. -/
theorem prepaid (hG : G.Simple) (u : G.ColorIndex) (V : MSbar.Heath.Voice G)
    (clear : MSbar.Heath.Clear G V) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Inventory G u V) s price := by
  intro C E flags programs wages baton
  obtain ⟨p,hb⟩ := MSbar.Ballet.paymentP (G:=G) price
  refine ⟨p,?_⟩
  intro l hl D w q Z post scouts pocket θ records P menu start quarter
  let M := WilsonWindowBookPurchase.raised s price l
  have prepared := fun i => hb i (D.L i) ((hl i).trans (D.large i).need)
  obtain ⟨W₁,h₁,H₁⟩ := MSbar.Alto.album hG θ M.K M.O (fun i=>(prepared i).pre) start
  obtain ⟨W₂,h₂,H₂⟩ := MSbar.Ballet.stage M.O M.K u V W₁ hG (chart_ok G) prepared clear
  obtain ⟨W₃,h₃,H₃⟩ := Mallow.loft W₂
  obtain ⟨W₄,h₄,H₄⟩ := Mallow.stocking Z W₃
  obtain ⟨W₅,h₅,H₅⟩ := OPE.Therm.poetry_delay W₄
  obtain ⟨W₆,h₆,H₆⟩ := all_packet_stage M.O M.K u V W₅ hG (chart_ok G) prepared clear
  refine ⟨W₆,h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))),?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η Q exchange aux rider booth sheltered works divides
  have tail := h₆.trans hY
  have dome := H₃.height Y (h₄.trans (h₅.trans tail)) bar wait B.a B.valid
  exact ⟨rfl,H₆ Y hY bar wait B.a B.valid,
    fun growth => ⟨H₁ Y (h₂.trans (h₃.trans (h₄.trans (h₅.trans tail)))) bar wait _ B.valid,
      H₂ Y (h₃.trans (h₄.trans (h₅.trans tail))) bar wait _ B.valid,dome.1,dome.2,growth⟩,
    H₄ Y (h₅.trans tail), H₅ Y tail wait B.a B.valid⟩

end YM.Integration.WilsonConditionalTaylorPurchase
end

