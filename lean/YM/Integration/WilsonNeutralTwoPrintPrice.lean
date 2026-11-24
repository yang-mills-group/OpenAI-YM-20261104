import YM.Integration.WilsonOriginalTwoPrintPhysicalPrice
import YM.Integration.WilsonNeutralTwoPrintAccount

/-! The two original physical receipts enter the thermal crop at their measured,
signed angular difference, including its marked constant. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPrice
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
variable {I X : Bool→Type} {Γ : Census V} {P : Bool→Passport n V}
variable (M : (a:Bool)→I a→Row (P a) Γ G (X a)) (w : Bool→V→ℝ) (grades : Bool→V→ℕ)
variable (x : (a:Bool)→X a) (ℓ : Bool→ℕ)
variable (B : BudgetPoint) {σ b K θ : Bool→ℝ} {p pieces depth : Bool→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Multi.Hot Γ) (v : V) (hv : v∈s.val.val)
variable (tube : LinkTube G) {k m j l D a₀ J : ℕ} {y o : Site n} {W ε : ℝ}
private def sign (a:Bool):ℝ:=if a then -1 else 1
open WilsonOriginalTwoPrintedRows
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "sum" => words M x sign ℓ
local notation "near" => (fun a=>early (M a) s.val m)
local notation "far" => (fun a=>late (M a) s.val m)
local notation "total" => (fun a=>picked (M a) s.val)
local notation "full" => (fun z:Chart G n=>sum total z.1 (increment 1 z.2))
local notation "fee" u:max => rent (G:=G) w sign ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
  (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s.val J u
local notation "paid" a:max => staff M w grades x B old scope a

local notation "hardCap" => WilsonEmittedLongInvoice.gross w sign (fun _=>0) B s.val m g p pieces depth b θ

local notation "left" => (fun U:Config G n=>(WilsonRootedKioskOccupiedSlip.bare
  (rendered (M false) B g) (x false) U).part s.val)
local notation "right" => (fun U:Config G n=>(WilsonRootedKioskOccupiedSlip.bare
  (rendered (M true) B g) (x true) U).part s.val)

local notation "cropAt" => B.B/32
local notation "out" m:max => WilsonEmittedLongInvoice.gross w sign (fun _=>0) B s.val m g p pieces depth b θ

include scope old hv in
theorem original (pole debt P₀ T:ℕ)(chosen:T=pole+debt+P₀)
    (closed:∀a:Bool,pole+0=ℓ a+(Launch.index Γ (grades a) s.val+1))
    (layout:Bool→Layout G)(tape:Bool→Finset Age)(legal:∀a,Legal (tape a) (layout a))
    (hε:0 ≤ ε)(winding:∀e,e+pole<3*T → ((e+pole).factorial:ℝ)*
      WilsonEmittedAngularJointFare.mass (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) (e+pole) ≤ ε)
    (same:∀a,(P a).origin v=o)(positive:0<g)(small:g ≤ 1/2)(depthOfTest:3*T ≤ J)
    (room:Room B n tube B.B W)(band:0 ≤ W)(held:W ≤ 2*g^(1/2:ℝ))
    {H β C:ℝ}(hp:0<H)(bp:0<β)(thermal:β ≤ 2*H)(clock:g=(Real.sqrt β)⁻¹)
    (size:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2 ≤ 102)
    (strip:∀a,WilsonEmittedCompactTariff.strip (σ a) ≤ θ a)
    (reserve:∀a,Real.exp ((σ a)⁻¹^2) ≤ H)(late:(256*((T:ℝ)+1))^2 ≤ Real.log H)
    (income:∀a,0 ≤ b a){grossPrice:Bool→ℝ}(hw:∀a v,0<w a v)
    (gross:∀a,WilsonRootedKioskOccupiedSlip.Gross (rendered (M a) B g) (w a) B.B (B.supportExponent+2) (grossPrice a))
    (cp:0 ≤ C)(jets:groupPrice tube 0*fee 0 ≤ C*(g^debt)⁻¹)(word:out 0 ≤ C*(g^debt)⁻¹):
    ∃r:WilsonOriginalOrdinaryFlatHulls.Row B tube o left right,
      r.price ≤ ((g^pole)⁻¹*(groupPrice tube 0*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)))*ε+
        (WilsonEmittedOutputPower.constant T+1)*C*g^P₀:=by
  have read:=WilsonNeutralTwoPrintAccount.read M x grades old s ⟨v,hv⟩ layout tape legal ℓ B scope
    pole (3*T) (fun a=>(closed a).symm) hε winding
  exact WilsonOriginalTwoPrintPhysicalPrice.original M w grades x ℓ B old scope s v hv tube
    pole debt P₀ T chosen closed hε read same positive small depthOfTest room band held hp bp thermal clock size tax
    strip reserve late income hw gross cp jets word

end YM.Integration.WilsonNeutralTwoPrintPrice
end
