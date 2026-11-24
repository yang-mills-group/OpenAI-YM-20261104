import YM.Integration.WilsonOlderFreshGraphCatalogueLaunch
import YM.Integration.WilsonEmittedLongInvoice

/-! One original declared lower catalogue on each basis letter, shared
by all lags of the true finite field transition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCatalogueRates
open Push.AbsoluteSums Push.Local WilsonOlderFreshGraphCatalogueLaunch
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density
open AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare
open WilsonEmittedCutGrouping WilsonEmittedGroupWallet WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G:Gauge}{n:Side}{d Q:ℕ}{σ:ℝ}{V:Type}[Fintype V] (T:V → Copy G d Q σ)
variable (y:Site n)(A:Unit → Set ℂ)
local notation "S₀" => WilsonOlderFreshGraphPointWallet.point y
local notation "marks" => (Stock.census Unit)
local notation "charges" => V × Fin (Q+1)
variable {B:BudgetPoint}{g K θ:ℝ}(scope:Invoice.Supports B K (B.supportExponent+2) g σ θ)
variable {ord seats shelf:ℕ}(mass:V → ℝ)(bill:∀v,(∑ j,(T v).fare j) ≤ mass v)
variable (cap:∀ t,‖value A t‖ ≤ 1)(order:Q ≤ ord)(width:1 ≤ seats)(height:d ≤ shelf)
variable (c:V×Fin (Q+1) → ℝ)(s:(Stock.census Unit).Mode)(hs:() ∈ s.val)
local notation "codes" => (fun _:charges=>fun _:Unit=>d)
local notation "wallet" w:max => (fun a:charges=>fun _:Unit=>w a.1)
local notation "leg" => (fun a:charges=>a.2.val)
local notation "M" => (book T y A)
local notation "nominal" a:max => (T a).rows S₀ A
local notation "nativePole" => (Launch.index marks (fun _:Unit=>d) s+1)


local notation "ord₀" => (fun _:charges=>ord)
local notation "seats₀" => (fun _:charges=>seats)
local notation "shelf₀" => (fun _:charges=>shelf)
local notation "one₀" => (fun _:charges=>(1:ℝ))
local notation "lengthFee" => (fun _:charges=>θ)
local notation "house" => (fun _:charges=>K)
local notation "billα" => (fun _:charges=>B.supportExponent+2)
local notation "draw" => (fun _ : charges=>d)
variable (w:V → ℝ)
variable (earned:∀v,Armada ((T v).rows (WilsonOlderFreshGraphPointWallet.point y) A) (fun _=>w v) (fun _=>d) σ 1 ord seats shelf)

include scope hs earned in
theorem jet (t:Affinity.Wallet A)(j m:ℕ)(μ:(a:charges)→(T a.1).Roster→Prop)
    (stay:∀a i,μ a i → s=(M a i).mode ∧ m ≤ (M a i).length)(z:Chart G n)(unit:‖z‖ ≤ 1):
    Through j (fun h:Chart G n=>WilsonEmittedFiledCatalogue.words M (fun _=>t) c leg μ h.1 (increment 1 h.2)) z
      (WilsonEmittedFiledCatalogue.rent (G:=G) (wallet w) c leg B
        (p:=ord₀) (pieces:=seats₀) (depth:=shelf₀) (b:=one₀) (α:=billα) (θ:=lengthFee) s j m):=by
  exact WilsonEmittedFiledCatalogue.funded M (wallet w) codes (fun _=>t) c leg B
    (fun a=>earned a.1) (fun _=>scope) s () hs j m μ stay z unit

include scope hs earned in
theorem long (m:ℕ):
    SumBudget (fun z:WilsonEmittedLongInvoice.Index M s m=>reservedMass B
      (WilsonEmittedLongInvoice.ground M B s m z) (WilsonEmittedLongInvoice.pay M c leg B s m z g))
      (WilsonEmittedLongInvoice.budget (G:=G) (wallet w) c leg B s m g ord₀ seats₀ shelf₀ house one₀ lengthFee) ∧
    SumBudget (fun z:WilsonEmittedLongInvoice.Index M s m=>reservedMass B
      (WilsonEmittedLongInvoice.ground M B s m z) (WilsonEmittedLongInvoice.crude M c leg s m z g ord₀ shelf₀))
      (WilsonEmittedLongInvoice.gross (wallet w) c leg B s m g ord₀ seats₀ shelf₀ one₀ lengthFee):=by
  exact ⟨WilsonEmittedLongInvoice.regular M (wallet w) codes c leg B (fun a=>earned a.1) (fun _=>scope) s () hs m,
    WilsonEmittedLongInvoice.rough M (wallet w) codes c leg B (fun a=>earned a.1) (fun _=>scope) s () hs m⟩

end YM.Integration.WilsonOlderFreshGraphCatalogueRates
end
