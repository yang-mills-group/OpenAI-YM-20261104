import YM.Integration.WilsonOriginalFiledGroupReturn
import YM.Integration.WilsonOriginalFiledRowScale

/-! The cropped, Laurent-restored row of two independently priced actual lamp catalogues. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoPrintedRows
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

include scope old hv in
theorem original {q₀:ℕ}(closed:∀a:Bool,q₀+0=ℓ a+(Launch.index Γ (grades a) s.val+1))
    (hε:0≤ε)(read:∀i<j,∑u:Fin i→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖≤ε)
    (same:∀a,(P a).origin v=o)(positive:0<g)(small:g≤1)(hj:j≤J)(hl:l≤j)
    (inside:2*m≤k)(apart:k<B.B)(room:Room B n tube B.B W)
    {C:Bool→ℝ}(hw:∀a v,0<w a v)
    (gross:∀a,WilsonRootedKioskOccupiedSlip.Gross (rendered (M a) B g) (w a) B.B (B.supportExponent+2) (C a)):
    ∃r:WilsonOriginalOrdinaryFlatHulls.Row B tube o left right,
      r.price=(g^q₀)⁻¹*(groupPrice tube 0*((l:ℝ)*((j:ℝ)*ε+fee 0*g^(j-l)+fee m)+fee 0*W^l)+g^q₀*hardCap):=by
  have widths:0≤B.supportExponent+2:=by linarith only [B.exponent_pos]
  have raw (U:Config G n)(a:Bool):Summable (fun i=>Spill.raw (M a) g (x a) i U):=
    (WilsonRootedKioskCompleteFiling.sums (rendered (M a) B g) (hw a) widths (gross a) (x a) U).1
  have identify:(left)-(right)=(g^q₀)⁻¹ • (sum total g-0):=by
    funext U
    have actual:=WilsonEmittedFiledCatalogue.numerical M w grades x sign ℓ B old scope s.val
      (ν:=fun _=>0) closed positive U (raw U)
    change (Spill.Foundry.uncut (M false) g (x false) U).part s.val-
      (Spill.Foundry.uncut (M true) g (x true) U).part s.val=_
    simpa [Fintype.sum_bool,sign,sub_eq_add_neg,add_comm] using actual.symm
  let r:WilsonOriginalOrdinaryFlatHulls.Row B tube o (sum total g) 0:=
    ⟨sum far g,l,J,W,(j:ℝ)*ε+fee 0*g^(j-l),fee 0,fee m,g^q₀*hardCap,
      WilsonOriginalFiledNativeCrop.original M w grades x sign (fun _=>0) ℓ B old scope s v hv tube
        closed hε read same positive small hj hl inside apart room⟩
  refine ⟨WilsonOriginalFiledRowScale.priced r (g^q₀)⁻¹ identify,?_⟩
  rw [WilsonOriginalFiledRowScale.price,abs_of_pos (inv_pos.mpr (pow_pos positive q₀))]
  rfl

end YM.Integration.WilsonOriginalTwoPrintedRows
end
