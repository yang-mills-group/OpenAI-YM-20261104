import YM.Integration.WilsonOlderFreshGraphCatalogueIncome

/-! One original declared lower catalogue on each basis letter, shared
by all lags of the true finite field transition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCatalogueLaunch
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
def book (a:V×Fin (Q+1)) := (T a.1).rows (WilsonOlderFreshGraphPointWallet.point y) A
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

include scope bill cap order width height in
theorem original : ∃w:V → ℝ,
    (∀v,0 < w v ∧ (w v)⁻¹ ≤ 1+mass v ∧
      Armada (nominal v) (fun _=>w v) (fun _=>d) σ 1 ord seats shelf) ∧
    (∀(a:charges)(t:Affinity.Wallet A),Air.Staff (M a) (fun j=>(M a j).paint t)
      (fun _=>d) σ (ord+shelf+1)) ∧
    ∀(t:Affinity.Wallet A)(U:Config G n),
      (g^nativePole)⁻¹ • WilsonEmittedFiledCatalogue.words M (fun _=>t) c leg
        (fun a=>WilsonEmittedCutGrouping.picked (M a) s) g U =
      ∑ a:charges,c a • (g^a.2.val • (Spill.Foundry.uncut (M a) g t U).part s):=by
  choose w hw hwallet old posted using (fun v=>WilsonOlderFreshGraphCatalogueIncome.original (T v) A scope
      y (bill v) cap order width height)
  have enrolled (a:charges) : Armada (M a) (fun _:Unit=>w a.1) (fun _:Unit=>d) σ 1 ord seats shelf := old a.1
  have rooms (a:charges):Invoice.Supports B K (B.supportExponent+2) g σ θ:=scope
  refine ⟨w,fun v=>⟨hw v,hwallet v,old v⟩,?_,?_⟩
  · intro a t
    exact WilsonEmittedFiledCatalogue.staff M (wallet w) codes (fun _=>t) B enrolled rooms a
  · intro t U
    apply WilsonEmittedFiledCatalogue.numerical M (wallet w) codes (fun _=>t) c leg B enrolled rooms s
      (ν:=leg) (fun a=>by change nativePole+a.2.val=a.2.val+nativePole;omega) scope.1
    exact fun a=>posted a.1 t U

end YM.Integration.WilsonOlderFreshGraphCatalogueLaunch
end
