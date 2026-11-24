import YM.Integration.WilsonOlderFreshGraphCatalogueRates
import YM.Integration.WilsonMeasuredImpulseCalendar

/-! The emitted cash register has its physical coarse budget and its
fine coupling. Convert just that coupling to the true coarse one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphInvoiceCurrency
open Lattice Wilson RG QuadraticLocal QuadraticLocal.Earn Push Push.AbsoluteSums
open Pressure PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics ConnectedActivityE6
open private relative from YM.Integration.WilsonMeasuredImpulseCalendar

theorem ratio {G:Gauge} (R:Run G)(simple:G.Simple){N per i:ℕ}(hi:i+1 ≤ N):
    regulatorRun R.family N per (i+1) ≤ 2*regulatorRun R.family N per i:=
  relative R.makes simple N per i (i+1) (Nat.le_succ i) hi

theorem shift {B:BudgetPoint} {g h K σ θ α:ℝ}
    (paid:Invoice.Supports B K α h σ θ)(earned:h ≤ 2*g)(gp:0<g)(cap:g≤1):
    Invoice.Supports B (2*K) α g σ θ:=by
  obtain ⟨_,_,one,s,hσ,hθ⟩:=paid
  refine ⟨gp,cap,by linarith,s.trans ?_,hσ,hθ⟩
  have nk:0≤K:=zero_le_one.trans one
  calc
    h*K ≤ (2*g)*K:=mul_le_mul_of_nonneg_right earned nk
    _ = g*(2*K):=by ring

theorem quote (G:Gauge)(B:BudgetPoint)(order seats:ℕ)(K α θ:ℝ):
    Invoice.price B (2*K) order seats α θ G=
    (2:ℝ)^order*Invoice.price B K order seats α θ G:=by
  unfold Invoice.price Footprint.payment Footprint.degreeIncome Invoice.liberty
  rw [mul_pow]
  ring

end YM.Integration.WilsonOlderFreshGraphInvoiceCurrency
end
