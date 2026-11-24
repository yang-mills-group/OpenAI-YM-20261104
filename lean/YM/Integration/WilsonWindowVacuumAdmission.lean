import YM.Integration.WilsonFundedWindowMenu
import YM.QuadraticLocal.Vacuum.Purchase

/-! The real vacuum admission on the register, menu and directed delay
of the original funded selector. The facility and wage floors are paid
before the length; the menu is known when the true physical lock is bought. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowVacuumAdmission

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source JointLoad JointLoad.Heir JointLoad.Heir.Suite
open JointLoad.Psalm Clockwork AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Geo ThroughLaunch Roof Push.PriceCompiler
open Further.StrongStartup SectorNext WilsonStartup Progress.DirectedRecipe Time
open Next.Foundations UVNext.CouplingReset Cub Circlet Graces Roost Pressure
open WilsonLimitConstruction.FundedCompanySelection

variable {G : Gauge}

def Ready : Prediction G := fun {_} {_} {A} F =>
  AllOrder.Transit.Lock F.shape F.v F.prices F.t F.span F.recordP (wind F.menu) A.delay

theorem prepaid (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Ready G) s price := by
  intro C E flags programs wages baton
  obtain ⟨n,facility⟩ := AllOrder.Transit.wagesWanted s price C E
  obtain ⟨m,pay⟩ := AllOrder.Transit.must s price E wages
  refine ⟨n ⊔ m,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨hn,hm⟩ := sup_le_iff.mp hl
  let M : Metals G := ⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩
  have facility' : AllOrder.Transit.Facility M.p M.K C E M.p.floorL := by
    intro x y stage L hL k hk width μ v o hw hμ rate j i
    exact facility x y stage L ((hn x).trans hL) k hk width μ v o hw hμ rate j i
  have hair : Roof.wantFacet M.p wages (1/16) M.p.floorL := by
    intro i j L step hL
    exact pay.hair i j L step ((hm j).trans hL)
  obtain ⟨W,hW,lock⟩ := AllOrder.Transit.locks (X := M) Z wages programs (rays s)
    mile stages (wind menu) hG facility' hair
    (fun i j _ => (E i j).reach.trans (by rw [(flags i j).2.2.2.1]; norm_num))
    (fun i j _ => by unfold rays; linarith [(s.profile j).price_pos]) quarter V
  refine ⟨W,hW,?_⟩
  intro Y hY bar wait hp directed archive origins shape
  dsimp only
  intro η rate exchange aux r booth sheltered works divides
  exact lock Y hY

end YM.Integration.WilsonWindowVacuumAdmission
end

