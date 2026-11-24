import YM.Integration.WilsonOriginalPrintedOrder

/-! The native B/32 length tariff for the two actual group prints at their
funded widths and on the physical thermal band. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoPrintPhysicalPrice
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
    (hε:0 ≤ ε)(read:∀i<3*T,∑u:Fin i→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖ ≤ ε)
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
  have coin:g^2=β⁻¹:=by rw [clock,inv_pow,Real.sq_sqrt bp.le]
  have invH:H⁻¹ ≤ g:=by
    have compare:H⁻¹ ≤ 2*g^2:=by
      rw [coin,←div_eq_mul_inv,←one_div]
      exact (div_le_div_iff₀ hp bp).mpr (by linarith)
    exact compare.trans (by nlinarith [mul_nonneg positive.le (sub_nonneg.mpr small)])
  have lengths (a:Bool):Real.exp (-(θ a))^cropAt ≤ g^T:=by
    have take:WilsonEmittedLengthWindow.strip (θ a) (σ a)=θ a:=
      max_eq_left (strip a)
    have aged:=(WilsonEmittedLengthWindow.decays (scope a) size (reserve a) tax T late).2
    rw [take,←inv_pow] at aged
    exact aged.trans (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) invH _)
  have wpos (a:Bool):0<Poly.toll (w a) s.val:=Poly.worth (hw a) s.val
  have tpos (a:Bool):0<θ a:=(scope a).2.2.2.2.2.2.1
  have regular:=WilsonOriginalPrintedLength.regular (G:=G) s.val w sign ℓ B
    (p:=p) (pieces:=pieces) (depth:=depth) (α:=fun _=>B.supportExponent+2)
    J cropAt wpos income tpos lengths
  have tail:=WilsonOriginalPrintedLength.unmasked s.val w sign (fun _=>0) B
    (p:=p) (pieces:=pieces) (depth:=depth) cropAt wpos income tpos positive lengths
  obtain ⟨r,price⟩:=WilsonOriginalTwoPrintedRows.original M w grades x ℓ B old scope s v hv tube
    (k:=2*cropAt) (m:=cropAt) (j:=3*T) (l:=2*T) closed hε read same positive (by linarith) depthOfTest
    (by omega) le_rfl (by have pos:=B.B_pos;omega) room hw gross
  refine ⟨r,price.le.trans ?_⟩
  exact WilsonOriginalPrintedOrder.original pole debt P₀ T chosen positive (by linarith) band held
    (price_nonneg tube 0) cp regular le_rfl (pow_nonneg positive.le _) jets
    (tail.trans (mul_le_mul_of_nonneg_right word (pow_nonneg positive.le _)))

end YM.Integration.WilsonOriginalTwoPrintPhysicalPrice
end
